use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::{
    alloc::Allocator,
    fmt,
    marker::{CoercePointee, PhantomData},
    mem::MaybeUninit,
    ptr::{self, NonNull},
};

use crate::{
    init::{Init, IntoInit},
    owned::Own,
    pin::{DropSlot, POwn},
    sealed,
    uninit::Uninit,
};

/// A place in memory that can hold an owned value of type `T`.
///
/// This trait makes [place expressions] explicit by providing methods to work
/// directly with the underlying memory location. A `Place` can be used to read
/// from or write to the memory location it represents.
///
/// Common types that can be referred to as places include `MaybeUninit<T>`,
/// arrays of `MaybeUninit<T>`, and smart pointers like `Box<MaybeUninit<T>>`,
/// `Rc<MaybeUninit<T>>`, and `Arc<MaybeUninit<T>>`, which is basically a
/// location in heap memory or on the current call stack.
///
/// # Safety
///
/// Implementors of this trait must ensure that the methods uphold their
/// contracts, particularly regarding the initialization state of the memory.
///
/// Specifically:
///
/// - The `as_mut_ptr` method must return a valid pointer to the memory location
///   of the place.
/// - The `assume_init` method must return the same memory location as an
///   initialized place containing a valid value of type `Self::Target`. The
///   validity of the place is the caller's responsibility to uphold.
/// - The `from_init` method must correctly wrap an initialized place containing
///   a valid value of type `Self::Target` into `Self`, discarding the explicit
///   initialization state. However, the wrapped value must still be valid
///   inside the place.
///
/// [place expressions]: https://doc.rust-lang.org/stable/reference/expressions.html#place-expressions-and-value-expressions
pub unsafe trait Place: Sized {
    /// The type of the value that this place can hold.
    type Target: ?Sized;

    /// The type of the place, but with an explicit initialized state.
    type Init;

    /// Returns a mutable pointer to the memory location of the place.
    fn as_mut_ptr(&mut self) -> *mut Self::Target;

    /// Assumes that the place is initialized and returns the initialized place.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the place is indeed initialized before
    /// calling this method. Failing to do so results in undefined behavior.
    /// See [`MaybeUninit::assume_init`] for more details.
    ///
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    unsafe fn assume_init(self) -> Self::Init;

    /// Discards the explicit initialization state and returns the place.
    fn from_init(init: Self::Init) -> Self;

    /// Initializes the place with the given initializer and returns an owned
    /// reference to the initialized value.
    ///
    /// This method is a convenience method of [`Uninit::from_mut`] +
    /// [`Uninit::write`], allowing direct initialization of a place without
    /// needing to wrap it in an `Uninit` first, which can be directly
    /// type-inferred by the compiler.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    /// use core::mem::MaybeUninit;
    ///
    /// let mut place = MaybeUninit::uninit();
    /// let owned = Place::write(&mut place, 42);
    /// assert_eq!(*owned, 42);
    /// ```
    fn write<'b, M, I>(&'b mut self, init: I) -> Own<'b, Self::Target>
    where
        I: IntoInit<'b, Self::Target, M, Init: Init<'b>, Error: fmt::Debug>,
    {
        Uninit::from_mut(self).write(init)
    }

    /// Initializes the place with the given initializer and returns a pinned
    /// owned reference to the initialized value.
    ///
    /// This method is a convenience method of [`Uninit::from_mut`] +
    /// [`Uninit::write_pin`], allowing direct pinned initialization of a place
    /// without needing to wrap it in an `Uninit` first, which can be directly
    /// type-inferred by the compiler.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{Place, drop_slot};
    /// use core::mem::MaybeUninit;
    ///
    /// let mut place = MaybeUninit::uninit();
    /// let drop_slot = drop_slot!();
    /// let owned = Place::write_pin(&mut place, 42, drop_slot);
    /// assert_eq!(*owned, 42);
    /// ```
    fn write_pin<'a, 'b, M, I>(
        &'a mut self,
        init: I,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> POwn<'b, Self::Target>
    where
        I: IntoInit<'b, Self::Target, M, Error: fmt::Debug>,
    {
        Uninit::from_mut(self).write_pin(init, slot)
    }
}

unsafe impl<T> Place for MaybeUninit<T> {
    type Target = T;

    type Init = T;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        self.as_mut_ptr()
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        Self::new(init)
    }
}

unsafe impl<T, const N: usize> Place for [MaybeUninit<T>; N] {
    type Target = [T; N];

    type Init = [T; N];

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        (self as &mut [MaybeUninit<T>]).as_mut_ptr() as *mut [T; N]
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.map(|p| MaybeUninit::assume_init(p)) }
    }

    fn from_init(init: Self::Init) -> Self {
        init.map(MaybeUninit::new)
    }
}

unsafe impl<T, A: Allocator> Place for Box<MaybeUninit<T>, A> {
    type Target = T;

    type Init = Box<T, A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        (**self).as_mut_ptr()
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let (raw, alloc) = Box::into_raw_with_allocator(init);
        unsafe { Box::from_raw_in(raw.cast::<MaybeUninit<T>>(), alloc) }
    }
}

unsafe impl<T, A: Allocator> Place for Box<[MaybeUninit<T>], A> {
    type Target = [T];

    type Init = Box<[T], A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        let len = self.len();
        let ptr = (**self).as_mut_ptr();
        ptr::slice_from_raw_parts_mut(ptr.cast::<T>(), len)
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let len = init.len();
        let (raw, alloc) = Box::into_raw_with_allocator(init);
        let ptr = ptr::slice_from_raw_parts_mut(raw.cast::<MaybeUninit<T>>(), len);
        unsafe { Box::from_raw_in(ptr, alloc) }
    }
}

unsafe impl<T, A: Allocator> Place for Rc<MaybeUninit<T>, A> {
    type Target = T;

    type Init = Rc<T, A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        Rc::get_mut(self).unwrap().as_mut_ptr()
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let (raw, alloc) = Rc::into_raw_with_allocator(init);
        unsafe { Rc::from_raw_in(raw.cast::<MaybeUninit<T>>(), alloc) }
    }
}

unsafe impl<T, A: Allocator> Place for Rc<[MaybeUninit<T>], A> {
    type Target = [T];

    type Init = Rc<[T], A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        let len = self.len();
        let ptr = Rc::get_mut(self).unwrap().as_mut_ptr();
        ptr::slice_from_raw_parts_mut(ptr.cast::<T>(), len)
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let len = init.len();
        let (raw, alloc) = Rc::into_raw_with_allocator(init);
        let ptr = ptr::slice_from_raw_parts(raw.cast::<MaybeUninit<T>>(), len);
        unsafe { Rc::from_raw_in(ptr, alloc) }
    }
}

unsafe impl<T, A: Allocator> Place for Arc<MaybeUninit<T>, A> {
    type Target = T;

    type Init = Arc<T, A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        Arc::get_mut(self).unwrap().as_mut_ptr()
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let (raw, alloc) = Arc::into_raw_with_allocator(init);
        unsafe { Arc::from_raw_in(raw.cast::<MaybeUninit<T>>(), alloc) }
    }
}

unsafe impl<T, A: Allocator> Place for Arc<[MaybeUninit<T>], A> {
    type Target = [T];

    type Init = Arc<[T], A>;

    fn as_mut_ptr(&mut self) -> *mut Self::Target {
        let len = self.len();
        let ptr = Arc::get_mut(self).unwrap().as_mut_ptr();
        ptr::slice_from_raw_parts_mut(ptr.cast::<T>(), len)
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        let len = init.len();
        let (raw, alloc) = Arc::into_raw_with_allocator(init);
        let ptr = ptr::slice_from_raw_parts(raw.cast::<MaybeUninit<T>>(), len);
        unsafe { Arc::from_raw_in(ptr, alloc) }
    }
}

/// A place state marker for owned places.
pub enum Owned {}
/// A place state marker for uninitialized places.
pub enum Uninitialized {}

/// A place state marker.
pub trait PlaceState: sealed::Sealed {
    #[doc(hidden)]
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(inner: *mut T);
}

impl sealed::Sealed for Owned {}
impl PlaceState for Owned {
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(inner: *mut T) {
        // SAFETY: The value is owned, so it is initialized.
        unsafe { inner.drop_in_place() };
    }
}

impl sealed::Sealed for Uninitialized {}
impl PlaceState for Uninitialized {
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(_inner: *mut T) {
        // No-op, as the value is uninitialized.
    }
}

/// A reference to a place in memory that can hold an owned value of type `T`.
///
/// `PlaceRef` can be in one of two states: [`Owned`] or [`Uninitialized`]. An
/// `Owned` place contains a fully initialized value of type `T`, while an
/// `Uninitialized` place is a location in memory that is reserved for a value
/// of type `T` but has not yet been initialized. The state of the place is
/// tracked at the type level using the `PlaceState` trait.
///
/// Users may find it easier to work with the type aliases [`Own`] and
/// [`Uninit`] instead of using `PlaceRef` directly.
#[derive(CoercePointee)]
#[repr(transparent)]
pub struct PlaceRef<'a, #[pointee] T: ?Sized, State: PlaceState> {
    pub(crate) inner: NonNull<T>,
    state: PhantomData<(State, &'a mut MaybeUninit<PhantomData<T>>)>,
    // See the drop implementation for details on why this is needed.
    owns_value: PhantomData<T>,
}

// General PlaceRef implementations

// SAFETY: PlaceRef is Send if T is Send.
unsafe impl<'a, T: ?Sized + Send, S: PlaceState> Send for PlaceRef<'a, T, S> {}
// SAFETY: PlaceRef is Sync if T is Sync.
unsafe impl<'a, T: ?Sized + Sync, S: PlaceState> Sync for PlaceRef<'a, T, S> {}

impl<'a, T: ?Sized, S: PlaceState> PlaceRef<'a, T, S> {
    pub(crate) const unsafe fn from_inner(inner: NonNull<T>) -> Self {
        PlaceRef {
            inner,
            state: PhantomData,
            owns_value: PhantomData,
        }
    }
}

// SAFETY: We have `owns_value: PhantomData<T>`, which tells the dropck that we
// own a value of type T.
unsafe impl<'a, #[may_dangle] T: ?Sized, S: PlaceState> Drop for PlaceRef<'a, T, S> {
    fn drop(&mut self) {
        // SAFETY: We are dropping the place, so we need to drop the value if it is
        // initialized.
        unsafe { S::drop::<T>(self.inner.as_ptr()) };
    }
}
