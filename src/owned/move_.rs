use core::{
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    mem::{self, Discriminant, ManuallyDrop, MaybeUninit},
    num::*,
    ptr::{self, NonNull},
    sync::atomic::*,
};

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
///     a: init::value(99).and(|i| *i += 1),
///     b: init::with(|| String::from("Hello")),
/// }));
/// let dst = uninit!(TestStruct);
/// let dst = src.move_to(dst);
/// assert_eq!(dst.a, 100);
/// assert_eq!(dst.b, "Hello");
/// ```
pub use placid_macro::Move;

use crate::{owned::Own, uninit::Uninit};

/// A trait enabling custom moving constructors.
///
/// This trait lets user types define how they can be moved into uninitialized
/// memory, which is useful for implementing efficient move semantics for types
/// that may not be trivially movable (e.g. due to `Drop` or `!Unpin`), or for
/// optimizing moves of large types by avoiding unnecessary copies.
///
/// The implemented type may not be `Sized`.
///
/// Trivially movable types are expected to implement `MoveToUninit` with
/// `IS_TRIVIAL = true` and perform a byte-wise move in `move_to_uninit`, but
/// users may find it necessary to implement it manually due to the limitations
/// of the Rust type system.
///
/// For structs that inherit their default move semantics from their fields, the
/// [`Move`] macro can be used to automatically generate the implementation by
/// recursively calling `move_to_uninit` on each field. The generated
/// implementation will be optimized to perform a byte-wise move if all fields
/// are trivially movable.
///
/// # Safety
///
/// Implementors must ensure that the `move_to_uninit` method performs a
/// byte-wise move of the value from `from` into `to` as long as
/// `Self::IS_TRIVIAL` is `true`.
///
/// The behavior is not constrained when `Self::IS_TRIVIAL` is `false`, but it
/// is recommended to still perform a move-like operation to avoid unexpected
/// behavior.
///
/// [`Move`]: crate::owned::Move
#[diagnostic::on_unimplemented(
    note = "implement `MoveToUninit` for `{Self}` manually or `#[derive(Move)]`"
)]
pub unsafe trait MoveToUninit {
    /// Whether the type is trivially movable, meaning that a byte-wise move is
    /// sufficient to transfer ownership of the value.
    const IS_TRIVIAL: bool = false;

    /// Moves the value into uninitialized memory, returning a new `Own` that
    /// owns the value at the new location.
    fn move_to_uninit<'d>(from: Own<'_, Self>, to: Uninit<'d, Self>) -> Own<'d, Self>;
}

macro_rules! impl_trivial_sized {
    ($($(@[$($g:tt)*])? $ty:ty),* $(,)?) => {$(
        unsafe impl<$($($g)*)?> MoveToUninit for $ty {
            const IS_TRIVIAL: bool = true;

            #[inline]
            fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
                let this = ManuallyDrop::new(from);
                // SAFETY: We are moving the value out of `this` and into `to`.
                unsafe { ptr::copy_nonoverlapping(&**this, to.as_mut_ptr(), 1) };
                // SAFETY: `to` is now initialized.
                unsafe { to.assume_init() }
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
            mem::forget(v.move_to(uninit));
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

    fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
        assert_eq!(
            from.len(),
            to.len(),
            "source slice length does not match destination slice length"
        );

        if T::IS_TRIVIAL {
            let this = ManuallyDrop::new(from);
            // SAFETY: We are moving the values out of `from` and into `to`.
            return unsafe {
                ptr::copy_nonoverlapping(this.as_ptr(), to.as_mut_ptr().cast::<T>(), this.len());
                to.assume_init()
            };
        }

        // SAFETY: We are moving the values out of `from` and into `to`.
        unsafe {
            let mut guard = SliceGuard::new(NonNull::new_unchecked(to.as_mut_ptr()));
            from.into_iter().for_each(|src| guard.initialize(src));
            guard.finish();
        }
        // SAFETY: `to` is now initialized.
        unsafe { to.assume_init() }
    }
}

unsafe impl<T: MoveToUninit, const N: usize> MoveToUninit for [T; N] {
    const IS_TRIVIAL: bool = T::IS_TRIVIAL;

    fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
        if T::IS_TRIVIAL {
            let this = ManuallyDrop::new(from);
            // SAFETY: We are moving the values out of `from` and into `to`.
            return unsafe {
                ptr::copy_nonoverlapping(this.as_ptr(), to.as_mut_ptr().cast::<T>(), N);
                to.assume_init()
            };
        }

        // SAFETY: We are moving the values out of `from` and into `to`.
        unsafe {
            let mut guard = SliceGuard::new(NonNull::new_unchecked(to.as_mut_ptr()));
            from.into_iter().for_each(|src| guard.initialize(src));
            guard.finish();
        }
        // SAFETY: `to` is now initialized.
        unsafe { to.assume_init() }
    }
}

unsafe impl MoveToUninit for str {
    const IS_TRIVIAL: bool = true;

    #[inline]
    fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
        assert_eq!(
            from.len(),
            to.len(),
            "source string length does not match destination string length"
        );

        // SAFETY: We are moving the value out of `from` and into `to`.
        unsafe {
            ptr::copy_nonoverlapping(from.as_ptr(), to.as_mut_ptr().cast::<u8>(), from.len());
            to.assume_init()
        }
    }
}

unsafe impl MoveToUninit for () {
    const IS_TRIVIAL: bool = true;

    #[inline]
    fn move_to_uninit<'d>(_: Own<'_, Self>, to: Uninit<'d, Self>) -> Own<'d, Self> {
        // SAFETY: `to` is now initialized.
        unsafe { to.assume_init() }
    }
}

macro_rules! impl_tuples {
    (@IMP $($ty:ident = ($src:ident, $dst:ident)),* $(,)?) => {
        unsafe impl<$($ty: MoveToUninit),*> MoveToUninit for ($($ty,)*) {
            const IS_TRIVIAL: bool = true $(&& $ty::IS_TRIVIAL)*;

            fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
                if Self::IS_TRIVIAL {
                    let this = ManuallyDrop::new(from);
                    // SAFETY: We are moving the value out of `from` and into `to`.
                    return unsafe {
                        ptr::copy_nonoverlapping(Own::as_ptr(&this), to.as_mut_ptr(), 1);
                        to.assume_init()
                    };
                }

                munge::munge!(let ($($src,)*) = from);
                munge::munge!(let ($($dst,)*) = to.by_ref());

                // SAFETY: We are moving the values out of `from` and into `to` by each field.
                // The initialized fields would be properly dropped at their destination if a
                // panic occurs during the move.
                unsafe {
                    $(let $dst = $src.move_to($dst);)*

                    mem::forget(($($dst),*));
                    to.assume_init()
                }
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
            fn move_to_uninit<'d>(from: Own<'_, Self>, mut to: Uninit<'d, Self>) -> Own<'d, Self> {
                // SAFETY: `Self` is #[repr(transparent)] over `T`, so it has the same size
                // and alignment as `T`. We are moving the value out of `from` and into `to`
                // by transmuting the references.
                unsafe {
                    let src = mem::transmute::<Own<'_, Self>, Own<'_, T>>(from);
                    let dst = mem::transmute::<Uninit<'_, Self>, Uninit<'_, T>>(to.by_ref());
                    mem::forget(src.move_to(dst));
                    to.assume_init()
                }
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
