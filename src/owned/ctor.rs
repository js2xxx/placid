use core::{
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    mem::{self, Discriminant, ManuallyDrop, MaybeUninit, size_of_val_raw},
    num::*,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    sync::atomic::*,
};

use crate::{fixed::Fix, owned::Own, uninit::Uninit};

/// A trait enabling custom copy constructors.
///
/// This trait lets user types define how they can be cloned into uninitialized
/// memory, which is useful for implementing efficient clone semantics for types
/// that may not be trivially clonable (e.g. due to `Drop` or `!Unpin`), or for
/// optimizing clones of large types by avoiding unnecessary copies.
///
/// The implemented type may not be `Sized`.
///
/// This trait is automatically implemented for any type that implements
/// [`CloneToUninit`] in the standard library, and wraps its implementation
/// safely to return an `Own` instead of writing into a raw pointer.
///
/// [``CloneToUninit``]: core::clone::CloneToUninit
pub trait CloneToUninit {
    /// Clones the value into uninitialized memory, returning a new fixed `Own`
    /// that owns the value at the new location.
    fn clone_to<'d>(&self, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>>;
}

impl<T: ?Sized + core::clone::CloneToUninit> CloneToUninit for T {
    #[inline]
    fn clone_to<'d>(&self, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        let src = self;
        let dst = to.into_raw();

        // SAFETY: The pointer metadata of `dst` is always valid since `Uninit<T>`
        // points to a valid uninitialized memory for `Self`.
        assert_eq!(
            mem::size_of_val(src),
            unsafe { mem::size_of_val_raw(dst) },
            "source and destination must have the same size"
        );

        let dst = dst.cast();
        // SAFETY: We are cloning the value into `to`.
        unsafe {
            core::clone::CloneToUninit::clone_to_uninit(src, dst);
            let ptr = ptr::from_raw_parts_mut(dst, ptr::metadata(src));
            Fix::new(Own::from_raw(ptr))
        }
    }
}

/// A trait enabling custom move constructors.
///
/// This trait lets user types define how they can be moved into uninitialized
/// memory, which is useful for implementing efficient move semantics for types
/// that may not be trivially movable (e.g. due to `Drop` or `!Unpin`), or for
/// optimizing moves of large types by avoiding unnecessary copies.
///
/// The implemented type may not be `Sized`.
///
/// Trivially movable types are expected to implement `MoveToUninit` with
/// `IS_TRIVIAL = true` and perform a byte-wise move in `move_to`, but users may
/// find it necessary to implement or [assert] it manually due to the
/// limitations of the Rust type system.
///
/// For structs that inherit their default move semantics from their fields, the
/// [`Move`] macro can be used to automatically generate the implementation by
/// recursively calling `move_to` on each field. The generated implementation
/// will be optimized to perform a byte-wise move if all fields are trivially
/// movable.
///
/// # Safety
///
/// Implementors must ensure that the `move_to` method performs a byte-wise move
/// of the value from `from` into `to` as long as `Self::IS_TRIVIAL` is `true`.
///
/// The behavior is not constrained when `Self::IS_TRIVIAL` is `false`, but it
/// is recommended to still perform a move-like operation to avoid unexpected
/// behavior.
///
/// The requirement is analogus to a correct implementation of `Clone` for a
/// type that is `Copy`, but enforces via a safety contract.
///
/// [`Move`]: crate::owned::Move
/// [assert]: crate::owned::AssertTrivialMove
#[diagnostic::on_unimplemented(
    note = "implement `MoveToUninit` for `{Self}` manually, `#[derive(Move)]`, or \
           wrap it in `AssertTrivialMove` if it is trivially movable"
)]
pub unsafe trait MoveToUninit {
    /// Whether the type is trivially movable, meaning that a byte-wise move is
    /// sufficient to transfer ownership of the value.
    const IS_TRIVIAL: bool = false;

    /// Moves the value into uninitialized memory, returning a new object that
    /// owns the value at the new location.
    fn move_to<'d>(from: Fix<Own<'_, Self>>, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>>;

    /// Moves the value into uninitialized memory, returning a new `Own` that
    /// owns the value at the new location.
    ///
    /// This method requires the implemented type to be trivially movable.
    #[inline]
    fn move_to_unfix<'d>(from: Own<'_, Self>, to: Uninit<'d, Self>) -> Own<'d, Self> {
        Fix::into_inner(Self::move_to(Fix::new(from), to))
    }
}

/// A simple wrapper around a type to assert that it is trivially movable.
///
/// This is useful for types that are naturally trivially movable but cannot be
/// automatically derived as such due to limitations of the Rust type system.
///
/// # Safety
///
/// `AssertTrivialMove<T>` asserts [trivial movability] for *any* `T`, so safe
/// code may relocate the wrapped value with a plain `memcpy` (and hand out
/// `&mut T`, `mem::swap` it, and so on).
///
/// This is sound because the only way to obtain an `AssertTrivialMove<T>` in
/// safe code is to wrap a `T` that is **already owned by value** (via the
/// `AssertTrivialMove(_)` constructor, plus unsizing coercions and clones of
/// such a value). This wrapper deliberately provides no [`Init`] / [`InitPin`]
/// or pinning projection, so it can never be built *in place* around a value
/// that lives only behind a [`Fix`] or [`POwn`], nor hand out a durable
/// [`Pin`]`<&mut T>` with which to install an address-dependent invariant. And
/// by Rust's move semantics, every by-value value is already
/// `memcpy`-relocatable: there are no move constructors, and `Pin` restricts
/// *access* to a value, never the movability of its bytes. A value whose
/// soundness depends on its own address therefore cannot be held by value, and
/// so can never reach this wrapper, which is what justifies `IS_TRIVIAL = true`
/// for whatever `T` actually ends up inside.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let func = own!(AssertTrivialMove(move |x| x + 1));
/// assert_eq!(func(41), 42);
/// ```
///
/// It can be further destructured using [`munge`](munge::munge!) to get the
/// inner value, though its moveability would be restricted by the wrapper:
///
/// ```rust
/// use placid::prelude::*;
///
/// let func = own!(AssertTrivialMove(move |x| x + 1));
/// munge::munge!(let AssertTrivialMove(original) = func);
/// // original: Own<impl Fn(i32) -> i32>
/// assert_eq!(original(41), 42);
/// ```
///
/// [`Pin`]: core::pin::Pin
/// [`Fix`]: crate::fixed::Fix
/// [`POwn`]: crate::pin::POwn
/// [`Init`]: crate::init::Init
/// [`InitPin`]: crate::init::InitPin
/// [trivial movability]: crate::owned::MoveToUninit::IS_TRIVIAL
#[derive(Debug)]
#[repr(transparent)]
pub struct AssertTrivialMove<T: ?Sized>(pub T);

impl<T: ?Sized> Deref for AssertTrivialMove<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> DerefMut for AssertTrivialMove<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

unsafe impl<T: ?Sized> MoveToUninit for AssertTrivialMove<T> {
    const IS_TRIVIAL: bool = true;

    #[inline]
    fn move_to<'d>(from: Fix<Own<'_, Self>>, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        let size = size_of_val::<T>(&**from);

        // SAFETY: We are moving the value properly.
        let src = unsafe { Own::into_raw(Fix::into_inner_unchecked(from)) };
        let dst = Uninit::into_raw(to);

        assert_eq!(
            size,
            // SAFETY: The pointer metadata of `dst` is always valid since `Uninit<T>`
            // points to a valid uninitialized memory for `Self`.
            unsafe { size_of_val_raw(dst) },
            "source slice length does not match destination slice length"
        );

        let dst = dst.cast::<u8>();
        // SAFETY: We are moving the value out of `src` and into `dst`.
        unsafe {
            ptr::copy_nonoverlapping(src.cast(), dst, size);
            let ptr = ptr::from_raw_parts_mut(dst, ptr::metadata(src));
            Fix::new(Own::from_raw(ptr))
        }
    }
}

/// Marks a type as structurally movable.
///
/// It provides a method to structurally move the value into an uninitialized
/// place by calling each field's custom move constructor.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// #[derive(Init, Move)]
/// struct TestStruct {
///     a: u32,
///     b: String,
/// }
///
/// let src: Own<TestStruct> = own!(init!(TestStruct {
///     a: init::value(99).and(|mut i| *i += 1),
///     b: init::with(|| String::from("Hello")),
/// }));
/// let dst = uninit!(TestStruct);
/// let dst = Fix::new(src).move_to(dst);
/// assert_eq!(dst.a, 100);
/// assert_eq!(dst.b, "Hello");
/// ```
pub use placid_macro::Move;

macro_rules! impl_trivial_sized {
    ($($(@[$($g:tt)*])? $ty:ty),* $(,)?) => {$(
        unsafe impl<$($($g)*)?> MoveToUninit for $ty {
            const IS_TRIVIAL: bool = true;

            #[inline]
            fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
                let this = ManuallyDrop::new(from);
                // SAFETY: We are moving the value out of `this` and into `to`.
                unsafe { ptr::copy_nonoverlapping(&**this, to.as_mut_ptr(), 1) };
                // SAFETY: `to` is now initialized.
                Fix::new(unsafe { to.assume_init() })
            }
        }
    )*};
}

impl_trivial_sized! {
    bool, char,
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    f32, f64,

    @[T: ?Sized] *const T, @[T: ?Sized] *mut T,
    @[T: ?Sized] &'_ T, @[T: ?Sized] &'_ mut T,

    NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize,
    NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
    @[T: ?Sized] NonNull<T>,

    AtomicI8, AtomicI16, AtomicI32, AtomicI64, AtomicIsize,
    AtomicU8, AtomicU16, AtomicU32, AtomicU64, AtomicUsize,
    @[T] AtomicPtr<T>,

    @[T] MaybeUninit<T>, @[T: ?Sized] PhantomData<T>,
    @[T] Discriminant<T>,

    core::alloc::Layout,
    core::ffi::c_void,
    core::net::IpAddr, core::net::Ipv4Addr, core::net::Ipv6Addr,
    core::net::SocketAddr, core::net::SocketAddrV4, core::net::SocketAddrV6,
    core::task::Waker, core::time::Duration,
}

#[cfg(feature = "alloc")]
impl_trivial_sized! {
    @[T: ?Sized] alloc::boxed::Box<T>,
    @[T: ?Sized] alloc::rc::Rc<T>, @[T: ?Sized] alloc::rc::Weak<T>,
    @[T: ?Sized] alloc::sync::Arc<T>, @[T: ?Sized] alloc::sync::Weak<T>,
    @[T] alloc::vec::Vec<T>,
    alloc::string::String,
    @[T] alloc::collections::VecDeque<T>,
    @[T] alloc::collections::LinkedList<T>,
    @[T] alloc::collections::BinaryHeap<T>,
    @[T] alloc::collections::BTreeSet<T>,
    @[K, V] alloc::collections::BTreeMap<K, V>,
}

#[cfg(feature = "std")]
impl_trivial_sized! {
    @[K] std::collections::HashSet<K>,
    @[K, V] std::collections::HashMap<K, V>,

    std::backtrace::Backtrace,
    std::hash::RandomState,
    std::fs::File, std::fs::Metadata, std::fs::Permissions, std::fs::FileType,
    std::fs::FileTimes, std::fs::DirEntry,
    std::io::Error, std::io::ErrorKind, std::io::SeekFrom,
    std::net::TcpListener, std::net::TcpStream, std::net::UdpSocket,
    std::path::PathBuf,
    std::process::Command, std::process::ExitStatus, std::process::Output,
    std::process::ExitCode, std::process::Child,
    std::sync::Once,
    std::thread::Thread, std::thread::ThreadId,
    std::time::Instant, std::time::SystemTime,
}

struct SliceGuard<T> {
    ptr: NonNull<[T]>,
    init: usize,
}

impl<T> Drop for SliceGuard<T> {
    fn drop(&mut self) {
        // SAFETY: We are dropping the initialized portion of the slice.
        unsafe {
            let ptr = NonNull::slice_from_raw_parts(self.ptr.cast::<T>(), self.init);
            ptr.drop_in_place();
        }
    }
}

impl<T: MoveToUninit> SliceGuard<T> {
    /// # Safety
    ///
    /// The caller must ensure that `ptr` points to a valid slice of
    /// uninitialized memory, and that `initialize` is called at most
    /// `ptr.len()` times with valid `Own<T>` values.
    unsafe fn new(ptr: NonNull<[T]>) -> Self {
        Self { ptr, init: 0 }
    }

    fn initialize(&mut self, v: Own<'_, T>) {
        unsafe {
            let ptr = self.ptr.cast::<T>().as_ptr().add(self.init);
            let uninit = Uninit::from_raw(ptr);
            mem::forget(T::move_to(Fix::new(v), uninit));
            self.init += 1;
        }
    }

    fn finish(self) {
        // SAFETY: We are forgetting the guard without dropping the
        // initialized portion of the slice, which is the caller's
        // responsibility.
        mem::forget(self)
    }
}

unsafe impl<T: MoveToUninit> MoveToUninit for [T] {
    const IS_TRIVIAL: bool = T::IS_TRIVIAL;

    fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        // SAFETY: We move the value out of `self` structurally.
        let from = unsafe { Fix::into_inner_unchecked(from) };
        assert_eq!(
            from.len(),
            to.len(),
            "source slice length does not match destination slice length"
        );

        if T::IS_TRIVIAL {
            let this = ManuallyDrop::new(from);
            // SAFETY: We are moving the values out of `from` and into `to`.
            return Fix::new(unsafe {
                ptr::copy_nonoverlapping(this.as_ptr(), to.as_mut_ptr().cast::<T>(), this.len());
                to.assume_init()
            });
        }

        // SAFETY: We are moving the values out of `from` and into `to`.
        unsafe {
            let mut guard = SliceGuard::new(NonNull::new_unchecked(to.as_mut_ptr()));
            from.into_iter().for_each(|src| guard.initialize(src));
            guard.finish();
        }
        // SAFETY: `to` is now initialized.
        Fix::new(unsafe { to.assume_init() })
    }
}

unsafe impl<T: MoveToUninit, const N: usize> MoveToUninit for [T; N] {
    const IS_TRIVIAL: bool = T::IS_TRIVIAL;

    fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        // SAFETY: We move the value out of `self` structurally.
        let from = unsafe { Fix::into_inner_unchecked(from) };

        if T::IS_TRIVIAL {
            let this = ManuallyDrop::new(from);
            // SAFETY: We are moving the values out of `from` and into `to`.
            return Fix::new(unsafe {
                ptr::copy_nonoverlapping(this.as_ptr(), to.as_mut_ptr().cast::<T>(), N);
                to.assume_init()
            });
        }

        // SAFETY: We are moving the values out of `from` and into `to`.
        unsafe {
            let mut guard = SliceGuard::new(NonNull::new_unchecked(to.as_mut_ptr()));
            from.into_iter().for_each(|src| guard.initialize(src));
            guard.finish();
        }
        // SAFETY: `to` is now initialized.
        Fix::new(unsafe { to.assume_init() })
    }
}

unsafe impl MoveToUninit for str {
    const IS_TRIVIAL: bool = true;

    #[inline]
    fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        // SAFETY: We move the value out of `from` structurally.
        let from = unsafe { Fix::into_inner_unchecked(from) };
        assert_eq!(
            from.len(),
            to.len(),
            "source string length does not match destination string length"
        );

        // SAFETY: We are moving the value out of `from` and into `to`.
        Fix::new(unsafe {
            ptr::copy_nonoverlapping(from.as_ptr(), to.as_mut_ptr().cast::<u8>(), from.len());
            to.assume_init()
        })
    }
}

unsafe impl MoveToUninit for () {
    const IS_TRIVIAL: bool = true;

    #[inline]
    fn move_to<'d>(_: Fix<Own<'_, Self>>, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
        // SAFETY: `to` is now initialized.
        Fix::new(unsafe { to.assume_init() })
    }
}

macro_rules! impl_tuples {
    (@IMP $($ty:ident = ($src:ident, $dst:ident)),* $(,)?) => {
        unsafe impl<$($ty: MoveToUninit),*> MoveToUninit for ($($ty,)*) {
            const IS_TRIVIAL: bool = true $(&& $ty::IS_TRIVIAL)*;

            fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>)
                -> Fix<Own<'d, Self>>
            {
                if Self::IS_TRIVIAL {
                    let this = ManuallyDrop::new(from);
                    // SAFETY: We are moving the value out of `from` and into `to`.
                    return Fix::new(unsafe {
                        ptr::copy_nonoverlapping(&**this, to.as_mut_ptr(), 1);
                        to.assume_init()
                    });
                }

                munge::munge!(let ($($src,)*) = from);
                munge::munge!(let ($($dst,)*) = to.by_ref());

                // SAFETY: We are moving the values out of `from` and into `to` by each field.
                // The initialized fields would be properly dropped at their destination if a
                // panic occurs during the move.
                Fix::new(unsafe {
                    $(let $dst = $ty::move_to($src, $dst);)*

                    mem::forget(($($dst),*));
                    to.assume_init()
                })
            }
        }
    };
    () => [];
    (
        $head:ident = ($head_src:ident, $head_dst:ident)
        $(, $tail:ident = ($tail_src:ident, $tail_dst:ident))* $(,)?
    ) => {
        impl_tuples!(@IMP $head = ($head_src, $head_dst), $($tail = ($tail_src, $tail_dst)),*);
        impl_tuples!($($tail = ($tail_src, $tail_dst)),*);
    };
}

impl_tuples! {
    A = (a_src, a_dst), B = (b_src, b_dst), C = (c_src, c_dst),
    D = (d_src, d_dst), E = (e_src, e_dst), F = (f_src, f_dst),
    G = (g_src, g_dst), H = (h_src, h_dst), I = (i_src, i_dst),
    J = (j_src, j_dst), K = (k_src, k_dst), L = (l_src, l_dst),
}

macro_rules! impl_single_derive {
    ($($([$($b:tt)*])? $ty:ident),* $(,)?) => {$(
        unsafe impl<T: MoveToUninit + $($($b)*)?> MoveToUninit for $ty<T> {
            const IS_TRIVIAL: bool = T::IS_TRIVIAL;

            #[inline]
            fn move_to<'d>(from: Fix<Own<'_, Self>>, mut to: Uninit<'d, Self>)
                -> Fix<Own<'d, Self>>
            {
                // SAFETY: `Self` is #[repr(transparent)] over `T`, so it has the same size
                // and alignment as `T`. We are moving the value out of `from` and into `to`
                // by transmuting the references.
                Fix::new(unsafe {
                    let src = mem::transmute::<Fix<Own<'_, Self>>, Fix<Own<'_, T>>>(from);
                    let dst = mem::transmute::<Uninit<'_, Self>, Uninit<'_, T>>(to.by_ref());
                    mem::forget(T::move_to(src, dst));
                    to.assume_init()
                })
            }
        }
    )*};
}

impl_single_derive! {
    Wrapping,
    [?Sized] Cell,
    [?Sized] UnsafeCell,
    [?Sized] ManuallyDrop,
}
