use core::{
    any::Any,
    borrow::{Borrow, BorrowMut},
    fmt,
    hash::{Hash, Hasher},
    marker::{CoercePointee, PhantomData},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::NonNull,
    slice,
};

use crate::{
    init::{Init, InitPin, InitPinResult, InitResult, IntoInit},
    pin::{DropSlot, POwn},
    sealed,
};

/// A place in memory that can hold an owned value of type `T`.
///
/// `Place` manages a region of memory that can either be uninitialized or
/// contain a fully initialized value of type `T`. The initialization state is
/// tracked at runtime using a boolean flag. When a `Place` is dropped, it
/// automatically drops the contained value if it is initialized.
///
/// Users may find it easier to work with the [`own!`], [`uninit!`], and
/// [`pown!`] macros instead of using `Place` directly.
///
/// [`own!`]: crate::own
/// [`uninit!`]: crate::uninit
/// [`pown!`]: crate::pown
#[repr(transparent)]
pub struct Place<T>(MaybeUninit<T>);

impl<T> Place<T> {
    /// A constant representing a new uninitialized place.
    pub const UNINIT: Self = Self::new();

    /// Creates a new uninitialized place.
    ///
    /// The returning place is initially uninitialized, meaning it does not
    /// contain a valid value of type `T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let mut place: Place<i32> = Place::new();
    /// // The place is uninitialized, so we can write a value to it.
    /// let owned = place.write(42);
    /// assert_eq!(*owned, 42);
    /// ```
    pub const fn new() -> Self {
        Place(MaybeUninit::uninit())
    }

    /// Creates a new place with its memory zeroed.
    ///
    /// The returning place is initially uninitialized, meaning it does not
    /// necessarily contain a valid value of type `T`. However, the memory is
    /// cleared to zero, which can be useful for types that have zero as a valid
    /// initialization value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let mut place: Place<u64> = Place::zeroed();
    /// // Memory is zeroed but uninitialized
    /// let owned = place.write(42u64);
    /// assert_eq!(*owned, 42);
    /// ```
    pub const fn zeroed() -> Self {
        Place(MaybeUninit::zeroed())
    }

    /// Creates a mutable reference to a place from a mutable reference to a
    /// `MaybeUninit<T>`.
    ///
    /// This allows converting existing `MaybeUninit` values into `Place`
    /// references for use with the place initialization API.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    /// use core::mem::MaybeUninit;
    ///
    /// let mut uninit: MaybeUninit<String> = MaybeUninit::uninit();
    /// let mut place = Place::from_mut(&mut uninit);
    /// let owned = place.write(String::from("Hello"));
    /// assert_eq!(&**owned, "Hello");
    /// ```
    pub const fn from_mut(r: &mut MaybeUninit<T>) -> &mut Self {
        // SAFETY: `Place` is a transparent wrapper around `MaybeUninit<T>`.
        unsafe { &mut *(r as *mut MaybeUninit<T> as *mut Place<T>) }
    }

    /// Returns an uninitialized reference to this place.
    ///
    /// This allows you to initialize the place using the various initialization
    /// methods provided by [`Uninit`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let mut place: Place<Vec<i32>> = Place::new();
    /// let uninit = place.uninit();
    /// let owned = uninit.write(vec![1, 2, 3]);
    /// assert_eq!(&*owned, &[1, 2, 3]);
    /// ```
    pub const fn uninit(&mut self) -> Uninit<'_, T> {
        let inner = NonNull::new(self.0.as_mut_ptr()).unwrap();
        unsafe { Uninit::from_inner(inner) }
    }

    /// Initializes the place with a value using the given initializer.
    ///
    /// This is a convenience method that combines `uninit()` and `write()` in
    /// one call.
    ///
    /// # Panics
    ///
    /// Panics if the initializer fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let mut place: Place<String> = Place::new();
    /// let owned = place.write(String::from("World"));
    /// assert_eq!(&**owned, "World");
    /// ```
    pub fn write<'a, I, Marker>(&'a mut self, init: I) -> Own<'a, T>
    where
        I: IntoInit<'a, T, Marker, Init: Init<'a>, Error: fmt::Debug>,
    {
        self.uninit().write(init)
    }

    /// Initializes the place with a pinned value using the given initializer.
    ///
    /// This is similar to `write()` but ensures the value remains pinned in
    /// memory, which is required for types that implement the pinning
    /// protocol.
    ///
    /// # Panics
    ///
    /// Panics if the initializer fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    /// use placid::pin::DroppingSlot;
    ///
    /// let mut place: Place<String> = Place::new();
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = place.write_pin(String::from("Pinned"), drop_slot);
    /// // The value is now pinned in memory
    /// ```
    pub fn write_pin<'a, 'b, I, Marker>(
        &'a mut self,
        init: I,
        slot: DropSlot<'a, 'b, T>,
    ) -> POwn<'b, T>
    where
        I: IntoInit<'b, T, Marker, Error: fmt::Debug>,
    {
        self.uninit().write_pin(init, slot)
    }
}

impl<T> Default for Place<T> {
    fn default() -> Self {
        Self::UNINIT
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

/// An owned reference that contains a fully initialized value of type `T`.
///
/// # Examples
///
/// ```rust
/// use placid::Own;
///
/// let mut my_place: Own<i32> = placid::own!(42);
/// assert_eq!(*my_place, 42);
/// *my_place += 1;
/// assert_eq!(*my_place, 43);
/// ```
pub type Own<'a, T> = PlaceRef<'a, T, Owned>;

/// An uninitialized reference that can hold a value of type `T`.
///
/// # Examples
///
/// ```rust
/// use placid::Uninit;
///
/// let my_place: Uninit<i32> = placid::uninit!();
/// ```
pub type Uninit<'a, T> = PlaceRef<'a, T, Uninitialized>;

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

// Owned PlaceRef implementations

/// Creates a new place initialized with the given expression.
///
/// The expression is evaluated and stored on the current call stack. The macro
/// then creates a `PlaceRef` pointing to that storage. This means the created
/// place is only valid within the scope it was created in.
///
/// # Examples
///
/// ```rust
/// let my_place = placid::own!(10);
/// assert_eq!(*my_place, 10);
/// ```
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! own {
    ($e:expr) => {{
        super let mut place = $crate::Place::UNINIT;
        place.write($e)
    }};
}

impl<'a, T: ?Sized> Deref for Own<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: PlaceRef is owned, so the value is initialized.
        unsafe { self.inner.as_ref() }
    }
}

impl<'a, T: ?Sized> DerefMut for Own<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: PlaceRef is owned, so the value is initialized.
        unsafe { self.inner.as_mut() }
    }
}

impl<'a, T: ?Sized> AsRef<T> for Own<'a, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> AsMut<T> for Own<'a, T> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T: ?Sized> Borrow<T> for Own<'a, T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> BorrowMut<T> for Own<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T: ?Sized> Own<'a, T> {
    /// Converts the owned reference into a pinned owned reference. If the value
    /// inside the place is not `!Unpin`, this ensures that it cannot be moved
    /// out of the place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let owned = placid::own!(String::from("Hello"));
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = placid::Own::into_pin(owned, drop_slot);
    /// // The value is now pinned and cannot be moved
    /// ```
    pub fn into_pin<'b>(this: Self, slot: DropSlot<'a, 'b, T>) -> POwn<'b, T> {
        POwn::new(this, slot)
    }

    /// Returns a raw pointer to the value inside the owned reference.
    ///
    /// The returned pointer is valid as long as the owned reference is valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let my_place = placid::own!(42i32);
    /// let ptr = placid::Own::as_ptr(&my_place);
    /// assert_eq!(unsafe { *ptr }, 42);
    /// ```
    pub const fn as_ptr(this: &Self) -> *const T {
        this.inner.as_ptr()
    }

    /// Returns a raw mutable pointer to the value inside the owned reference.
    ///
    /// The returned pointer is valid as long as the owned reference is valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut my_place = placid::own!(42i32);
    /// let ptr = placid::Own::as_mut_ptr(&mut my_place);
    /// unsafe { *ptr = 100; }
    /// assert_eq!(*my_place, 100);
    /// ```
    pub const fn as_mut_ptr(this: &mut Self) -> *mut T {
        this.inner.as_ptr()
    }

    /// Leaks the value inside the owned reference, returning a mutable
    /// reference with the same lifetime as the place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Own;
    /// let my_place: Own<String> = placid::own!(String::from("Hello"));
    /// let leaked_str: &mut String = Own::leak(my_place);
    /// leaked_str.push_str(", world!");
    /// assert_eq!(leaked_str, "Hello, world!");
    /// #
    /// # // Clean up to avoid leak in test
    /// # unsafe { core::ptr::from_mut(leaked_str).drop_in_place() };
    /// ```
    pub const fn leak(this: Self) -> &'a mut T {
        let mut inner = this.inner;
        mem::forget(this);
        // SAFETY: We have exclusive ownership of the value, so we can return a
        // mutable reference to it.
        unsafe { inner.as_mut() }
    }

    /// Converts the owned reference into a raw pointer, consuming the original
    /// object.
    ///
    /// The caller is responsible for managing the memory and ensuring that the
    /// value is properly dropped when no longer needed. The memory itself
    /// remains valid for the original lifetime of the place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let my_place = placid::own!(String::from("Hello"));
    /// let ptr = placid::Own::into_raw(my_place);
    /// unsafe {
    ///     let recovered = placid::Own::from_raw(ptr);
    ///     assert_eq!(&*recovered, "Hello");
    /// }
    /// ```
    pub const fn into_raw(this: Self) -> *mut T {
        let inner = this.inner;
        mem::forget(this);
        inner.as_ptr()
    }

    /// Creates an owned reference from a raw pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is previously obtained from
    /// [`Own::into_raw`] and that the value is still valid and initialized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Own;
    ///
    /// let my_place = placid::own!(vec![1, 2, 3]);
    /// let ptr = Own::into_raw(my_place);
    /// let recovered: Own<Vec<i32>> = unsafe { Own::from_raw(ptr) };
    /// assert_eq!(&*recovered, &[1, 2, 3]);
    /// ```
    pub const unsafe fn from_raw(ptr: *mut T) -> Self {
        // SAFETY: The caller must ensure that the pointer is valid and points to
        // an initialized value.
        let inner = unsafe { NonNull::new_unchecked(ptr) };
        unsafe { Own::from_inner(inner) }
    }

    /// Drops the value inside the place and converts it into an uninitialized
    /// reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{Own, Uninit};
    ///
    /// let my_place: Own<String> = placid::own!(String::from("Hello"));
    /// let uninit_place: Uninit<String> = Own::drop(my_place);
    /// // At this point, the String has been dropped.
    /// // We can now re-initialize the place.
    /// let my_place_again: Own<String> = uninit_place.write(String::from("World"));
    /// assert_eq!(&*my_place_again, "World");
    /// ```
    pub fn drop(this: Self) -> Uninit<'a, T> {
        let inner = this.inner;
        mem::forget(this);

        // SAFETY: We have exclusive ownership of the value, so we can drop it.
        unsafe { inner.drop_in_place() };
        unsafe { Uninit::from_inner(inner) }
    }
}

impl<'a, T> Own<'a, T> {
    /// Takes the value out of the owned reference, leaving it uninitialized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{Own, Uninit};
    ///
    /// let my_place: Own<i32> = placid::own!(100);
    /// let (value, uninit_place): (i32, Uninit<i32>) = Own::take(my_place);
    /// assert_eq!(value, 100);
    /// // The place is now uninitialized, we can re-initialize it.
    /// let my_place_again: Own<i32> = uninit_place.write(200);
    /// assert_eq!(*my_place_again, 200);
    /// ```
    pub const fn take(this: Self) -> (T, Uninit<'a, T>) {
        let inner = this.inner;
        mem::forget(this);
        // SAFETY: We have exclusive ownership of the value, so we can take it out.
        let value = unsafe { inner.read() };
        let place = unsafe { Uninit::from_inner(inner) };
        (value, place)
    }
}

macro_rules! impl_downcast {
    ($([$($t:tt)*])*) => {$(
        impl<'a> Own<'a, dyn $($t)*> {
            /// Attempts to downcast the owned reference to a concrete type.
            ///
            /// # Errors
            ///
            /// Returns the original owned reference if the downcast fails.
            ///
            /// # Examples
            ///
            /// ```rust,ignore
            /// use placid::{Own, own};
            /// use std::any::Any;
            ///
            #[doc = concat!("let value: Own<dyn ", stringify!($($t)*), "> = own!(42i32);")]
            /// match value.downcast::<i32>() {
            ///     Ok(owned) => assert_eq!(*owned, 42),
            ///     Err(_) => panic!("Downcast failed"),
            /// }
            /// ```
            pub fn downcast<U: $($t)*>(self) -> Result<Own<'a, U>, Self> {
                if (*self).is::<U>() {
                    // SAFETY: We have checked that the type is correct.
                    Ok(unsafe { self.downcast_unchecked() })
                } else {
                    Err(self)
                }
            }

            /// Downcasts the owned reference to a concrete type without
            /// checking.
            ///
            /// # Safety
            ///
            /// The caller must ensure that the type is correct.
            ///
            /// # Examples
            ///
            /// ```rust,ignore
            /// use placid::{Own, own};
            /// use std::any::Any;
            ///
            #[doc = concat!("let value: Own<dyn ", stringify!($($t)*), "> = own!(\"hello\");")]
            /// let downcast: Own<&str> = unsafe { value.downcast_unchecked() };
            /// ```
            pub unsafe fn downcast_unchecked<U: $($t)*>(self) -> Own<'a, U> {
                let raw = Own::into_raw(self).cast::<U>();
                // SAFETY: The caller must ensure that the type is correct.
                unsafe { Own::from_raw(raw) }
            }
        }
    )*};
}

impl_downcast!([Any][Any + Send][Any + Send + Sync]);

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for Own<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for Own<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized> fmt::Pointer for Own<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.inner, f)
    }
}

impl<'a, T: Clone> Own<'a, T> {
    pub fn clone<'b>(&self, to: &'b mut Place<T>) -> Own<'b, T> {
        to.write(|| (**self).clone())
    }
}

impl<'a, T: Default> Own<'a, T> {
    pub fn default(place: &'a mut Place<T>) -> Self {
        place.write(T::default)
    }
}

impl<'a, T> Default for Own<'a, [T]> {
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_mut(&mut [])) }
    }
}

impl<'a> Default for Own<'a, str> {
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_ref("")) }
    }
}

impl<'a> Default for Own<'a, core::ffi::CStr> {
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_ref(c"")) }
    }
}

impl<'a, 'b, T: ?Sized + PartialEq<U>, U: ?Sized> PartialEq<Own<'b, U>> for Own<'a, T> {
    fn eq(&self, other: &Own<'b, U>) -> bool {
        **self == **other
    }
}

impl<'a, T: ?Sized + Eq> Eq for Own<'a, T> {}

impl<'a, 'b, T: ?Sized + PartialOrd<U>, U: ?Sized> PartialOrd<Own<'b, U>> for Own<'a, T> {
    fn partial_cmp(&self, other: &Own<'b, U>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<'a, T: ?Sized + Ord> Ord for Own<'a, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<'a, T: ?Sized + Hash> Hash for Own<'a, T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<'a, T: ?Sized + Hasher> Hasher for Own<'a, T> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes);
    }
}

#[cfg(feature = "fn-impl")]
mod fn_impl;

// Uninitialized PlaceRef implementations

/// Creates a new uninitialized place on the stack.
///
/// The macro returns an [`Uninit`] reference that can later be written to. A
/// typed variant is available by passing a type parameter.
///
/// # Examples
///
/// ```rust
/// let my_uninit_place: placid::Uninit<u32> = placid::uninit!();
/// let my_typed_uninit_place = placid::uninit!(u64);
/// ```
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! uninit {
    () => {{
        super let mut place = $crate::Place::UNINIT;
        place.uninit()
    }};
    ($ty:ty) => {{
        super let mut place = $crate::Place::<$ty>::UNINIT;
        place.uninit()
    }};
}

impl<'a, T> Deref for Uninit<'a, T> {
    type Target = MaybeUninit<T>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: We are treating the place as uninitialized.
        unsafe { self.inner.as_uninit_ref() }
    }
}

impl<'a, T> DerefMut for Uninit<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: We are treating the place as uninitialized.
        unsafe { self.inner.as_uninit_mut() }
    }
}

impl<'a, T> Deref for Uninit<'a, [T]> {
    type Target = [MaybeUninit<T>];

    fn deref(&self) -> &Self::Target {
        // SAFETY: We are treating the place as uninitialized.
        unsafe {
            let data = self.inner.as_ptr();
            slice::from_raw_parts(data.cast(), data.len())
        }
    }
}

impl<'a, T> DerefMut for Uninit<'a, [T]> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: We are treating the place as uninitialized.
        unsafe {
            let data = self.inner.as_ptr();
            slice::from_raw_parts_mut(data.cast(), data.len())
        }
    }
}

impl<'a, T: ?Sized> Uninit<'a, T> {
    /// Returns a raw mutable pointer to the uninitialized value inside the
    /// reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut uninit: placid::Uninit<i32> = placid::uninit!();
    /// let ptr = uninit.as_mut_ptr();
    /// unsafe {
    ///     std::ptr::write(ptr, 42);
    ///     // Now the value at ptr is initialized to 42
    ///     assert_eq!(*uninit.assume_init(), 42);
    /// }
    /// ```
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_ptr()
    }

    /// Assumes that the reference is initialized and converts it into an owned
    /// reference.
    ///
    /// For the pinning variant, see [`Uninit::assume_init_pin`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that the value is indeed initialized before
    /// calling this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut uninit: placid::Uninit<i32> = placid::uninit!(i32);
    /// unsafe {
    ///     std::ptr::write(uninit.as_mut_ptr(), 42);
    ///     // Now assume it's initialized and recover the owned reference
    ///     assert_eq!(*uninit.assume_init(), 42);
    /// }
    /// ```
    pub unsafe fn assume_init(self) -> Own<'a, T> {
        let inner = self.inner;
        mem::forget(self);
        unsafe { Own::from_inner(inner) }
    }

    /// Assumes that the reference is initialized and converts it into a pinned
    /// & owned reference.
    ///
    /// The pinning variant is needed when the value inside the reference is
    /// invalid if not in a pinned location. The semantics are slightly
    /// different from `Own::into_pin(place.assume_init())`, where an
    /// unpinned [`Own`]ed reference is exposed temporarily during the
    /// expression.
    ///
    /// For the non-pinning variant, see [`Uninit::assume_init`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that the value is indeed initialized before
    /// calling this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::drop_slot;
    ///
    /// // Initialize a value in place first
    /// let mut uninit = placid::uninit!(String);
    /// let drop_slot = drop_slot!();
    /// unsafe {
    ///     uninit.as_mut_ptr().write(String::from("Pinned value"));
    ///
    ///     // Then assume it's initialized and convert to pinned
    ///     let pinned = uninit.assume_init_pin(drop_slot);
    ///     assert_eq!(&*pinned, "Pinned value");
    /// }
    /// ```
    pub unsafe fn assume_init_pin<'b>(self, slot: DropSlot<'a, 'b, T>) -> POwn<'b, T> {
        let inner = self.inner;
        mem::forget(self);
        POwn::new(unsafe { Own::from_inner(inner) }, slot)
    }

    /// Initializes the reference with the given initializer and returns the
    /// owned reference.
    ///
    /// # Panics
    ///
    /// This method panics if the initializer returns an error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let uninit = placid::uninit!(String);
    /// let owned = uninit.write(String::from("Initialized!"));
    /// assert_eq!(&*owned, "Initialized!");
    /// ```
    pub fn write<I, Marker>(self, init: I) -> Own<'a, T>
    where
        I: IntoInit<'a, T, Marker, Init: Init<'a>, Error: fmt::Debug>,
    {
        self.try_write(init).unwrap()
    }

    /// Tries to initialize the reference with the given initializer and returns
    /// the owned reference.
    ///
    /// # Errors
    ///
    /// This method returns an error if the initializer fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let uninit = placid::uninit!(i32);
    /// let result = uninit.try_write(42);
    /// assert!(result.is_ok());
    /// ```
    pub fn try_write<I, Marker>(self, init: I) -> InitResult<'a, I::Init>
    where
        I: IntoInit<'a, T, Marker, Init: Init<'a>>,
    {
        init.into_init().init(self)
    }

    /// Initializes the reference with the given initializer and returns the
    /// pinned & owned reference.
    ///
    /// # Panics
    ///
    /// This method panics if the initializer returns an error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let uninit = placid::uninit!(String);
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = uninit.write_pin(String::from("Pinned value"), drop_slot);
    /// // The value is now pinned and initialized
    /// assert_eq!(&*pinned, "Pinned value");
    /// ```
    pub fn write_pin<'b, I, Marker>(self, init: I, slot: DropSlot<'a, 'b, T>) -> POwn<'b, T>
    where
        I: IntoInit<'b, T, Marker, Error: fmt::Debug>,
    {
        self.try_write_pin(init, slot).unwrap()
    }

    /// Tries to initialize the reference with the given pinning initializer and
    /// returns the pinned & owned reference.
    ///
    /// # Errors
    ///
    /// This method returns an error if the initializer fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let uninit = placid::uninit!(Vec<i32>);
    /// let drop_slot = placid::drop_slot!();
    /// let result = uninit.try_write_pin(vec![1, 2, 3], drop_slot);
    /// assert!(result.is_ok());
    /// ```
    pub fn try_write_pin<'b, I, Marker>(
        self,
        init: I,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, I::Init>
    where
        I: IntoInit<'b, T, Marker>,
    {
        init.into_init().init_pin(self, slot)
    }
}

impl<'a, T: ?Sized> fmt::Debug for Uninit<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Uninit<{}>", core::any::type_name::<T>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_place_macro() {
        let my_place = own!(10);
        assert_eq!(*my_place, 10);
    }

    #[test]
    fn test_own_take() {
        let my_place = own!(100);
        let (value, uninit_place) = Own::take(my_place);
        assert_eq!(value, 100);
        let my_place_again = uninit_place.write(200);
        assert_eq!(*my_place_again, 200);
    }
}
