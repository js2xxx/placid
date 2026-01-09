use core::{
    fmt,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::NonNull,
    slice,
};

use crate::{
    init::{Init, InitPin, InitPinResult, InitResult, IntoInit},
    owned::Own,
    pin::{DropSlot, POwn},
    place::{Place, PlaceRef, Uninitialized},
};

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
        super let mut place = ::core::mem::MaybeUninit::uninit();
        $crate::Uninit::from_mut(&mut place)
    }};
    ($ty:ty) => {{
        super let mut place = ::core::mem::MaybeUninit::<$ty>::uninit();
        $crate::Uninit::from_mut(&mut place)
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
    /// Converts the uninitialized reference into a raw pointer, consuming the
    /// original object.
    ///
    /// The caller is responsible for managing the memory and ensuring that the
    /// value is properly initialized and dropped when no longer needed. The
    /// memory itself remains valid for the original lifetime of the place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut uninit: placid::Uninit<String> = placid::uninit!();
    /// let ptr = placid::Uninit::into_raw(uninit);
    /// unsafe {
    ///     std::ptr::write(ptr, String::from("Hello"));
    ///     let owned = placid::Own::from_raw(ptr);
    ///     assert_eq!(&*owned, "Hello");
    /// }
    /// ```
    pub const fn into_raw(self) -> *mut T {
        let inner = self.inner;
        mem::forget(self);
        inner.as_ptr()
    }

    /// Creates an uninitialized reference from a raw pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid and points to
    /// uninitialized memory for type `T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut buffer = std::mem::MaybeUninit::uninit();
    /// let ptr = buffer.as_mut_ptr();
    /// let mut uninit: placid::Uninit<i32> = unsafe { placid::Uninit::from_raw(ptr) };
    /// unsafe {
    ///     std::ptr::write(uninit.as_mut_ptr(), 42);
    ///     let owned = uninit.assume_init();
    ///     assert_eq!(*owned, 42);
    /// }
    /// ```
    pub const unsafe fn from_raw(ptr: *mut T) -> Self {
        let inner = unsafe { NonNull::new_unchecked(ptr) };
        unsafe { Uninit::from_inner(inner) }
    }

    /// Creates an uninitialized reference from a mutable place.
    ///
    /// This method is the de facto safe way to create an `Uninit` reference
    /// without using raw pointers or macros.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut buffer = std::mem::MaybeUninit::uninit();
    /// let mut uninit: placid::Uninit<i32> = placid::Uninit::from_mut(&mut buffer);
    /// unsafe {
    ///     std::ptr::write(uninit.as_mut_ptr(), 42);
    ///     let owned = uninit.assume_init();
    ///     assert_eq!(*owned, 42);
    /// }
    /// ```
    pub fn from_mut(place: &'a mut impl Place<Target = T>) -> Self {
        // SAFETY: We have a mutable reference to a place, so the memory is
        // valid for T.
        unsafe { Self::from_raw(place.as_mut_ptr()) }
    }

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
