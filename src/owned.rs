use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::{
    alloc::Allocator,
    any::Any,
    borrow::{Borrow, BorrowMut},
    fmt,
    hash::{Hash, Hasher},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use crate::{
    pin::{DropSlot, POwn},
    place::{Owned, Place, PlaceRef},
    uninit::Uninit,
};

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
        super let mut place = ::core::mem::MaybeUninit::uninit();
        $crate::Place::write(&mut place, $e)
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

    /// Creates an owned reference from a mutable place.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the place is fully initialized and
    /// valid for the lifetime `'a`.
    ///
    /// For the safe counterpart, see [`Uninit::from_mut`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{Place, Own, Uninit};
    /// use core::mem::MaybeUninit;
    ///
    /// let mut uninit_place = MaybeUninit::new(10);
    /// let owned_place: Own<i32> = unsafe { Own::from_mut(&mut uninit_place) };
    /// assert_eq!(*owned_place, 10);
    /// ```
    pub unsafe fn from_mut(place: &'a mut impl Place<Target = T>) -> Self {
        unsafe { Own::from_raw(place.as_mut_ptr()) }
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
    pub fn clone<'b>(&self, to: &'b mut impl Place<Target = T>) -> Own<'b, T> {
        to.write(|| (**self).clone())
    }
}

impl<'a, T: Default> Own<'a, T> {
    pub fn default(place: &'a mut impl Place<Target = T>) -> Self {
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

/// A trait for types that can be converted into owned places.
pub trait IntoOwn: Deref {
    type Place: Place<Target = Self::Target, Init = Self>;

    #[doc(hidden)]
    fn into_own_place(self) -> Self::Place {
        Place::from_init(self)
    }
}

impl<T, A: Allocator> IntoOwn for Box<T, A> {
    type Place = Box<MaybeUninit<T>, A>;
}

impl<T, A: Allocator> IntoOwn for Box<[T], A> {
    type Place = Box<[MaybeUninit<T>], A>;
}

impl<T, A: Allocator> IntoOwn for Rc<T, A> {
    type Place = Rc<MaybeUninit<T>, A>;
}

impl<T, A: Allocator> IntoOwn for Rc<[T], A> {
    type Place = Rc<[MaybeUninit<T>], A>;
}

impl<T, A: Allocator> IntoOwn for Arc<T, A> {
    type Place = Arc<MaybeUninit<T>, A>;
}

impl<T, A: Allocator> IntoOwn for Arc<[T], A> {
    type Place = Arc<[MaybeUninit<T>], A>;
}

#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! into_own {
    ($p:ident <- $e:expr) => {{
        $p = $crate::owned::IntoOwn::into_own_place($e);
        unsafe { $crate::Own::from_mut(&mut $p) }
    }};
    ($e:expr) => {{
        super let mut p = $crate::owned::IntoOwn::into_own_place($e);
        unsafe { $crate::Own::from_mut(&mut p) }
    }};
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

    #[test]
    fn test_into_own() {
        let mut my_place;
        let owned = into_own!(my_place <- Box::new(55));
        assert_eq!(*owned, 55);
        drop(owned);
        my_place.write(123);

        let owned2 = into_own!(Box::new(77));
        assert_eq!(*owned2, 77);
    }
}
