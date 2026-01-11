//! Owned references and related utilities.
//!
//! This module provides the [`Own<T>`] type, which represents an owned
//! reference to a fully initialized value in a place. It also includes macros
//! and traits for creating and manipulating owned references.
//!
//! For constructing owned references onto the stack, see the [`own!`] macro.
//!
//! For converting containers into owned references, see the [`IntoOwn`] trait
//! and the [`into_own!`] macro.
//!
//! [`Own<T>`]: crate::owned::Own
//! [`own!`]: crate::own
//! [`IntoOwn`]: crate::owned::IntoOwn
//! [`into_own!`]: crate::into_own

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, rc::Rc, sync::Arc};
#[cfg(feature = "alloc")]
use core::{alloc::Allocator, mem::MaybeUninit};
use core::{
    any::Any,
    borrow::{Borrow, BorrowMut},
    error::Error,
    fmt,
    hash::{Hash, Hasher},
    mem,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::NonNull,
    task::{Context, Poll},
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
/// use placid::prelude::*;
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
        $crate::place::Place::write(&mut place, $e)
    }};
}

impl<'a, T: ?Sized> Deref for Own<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: PlaceRef is owned, so the value is initialized.
        unsafe { self.inner.as_ref() }
    }
}

impl<'a, T: ?Sized> DerefMut for Own<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: PlaceRef is owned, so the value is initialized.
        unsafe { self.inner.as_mut() }
    }
}

impl<'a, T: ?Sized> AsRef<T> for Own<'a, T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> AsMut<T> for Own<'a, T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T: ?Sized> Borrow<T> for Own<'a, T> {
    #[inline]
    fn borrow(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> BorrowMut<T> for Own<'a, T> {
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let owned = own!(String::from("Hello"));
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// // The value is now pinned and cannot be moved
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let my_place = own!(42i32);
    /// let ptr = Own::as_ptr(&my_place);
    /// assert_eq!(unsafe { *ptr }, 42);
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let mut my_place = own!(42i32);
    /// let ptr = Own::as_mut_ptr(&mut my_place);
    /// unsafe { *ptr = 100; }
    /// assert_eq!(*my_place, 100);
    /// ```
    #[inline]
    pub const fn as_mut_ptr(this: &mut Self) -> *mut T {
        this.inner.as_ptr()
    }

    /// Leaks the value inside the owned reference, returning a mutable
    /// reference with the same lifetime as the place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let my_place = own!(String::from("Hello"));
    /// let leaked_str: &mut String = Own::leak(my_place);
    /// leaked_str.push_str(", world!");
    /// assert_eq!(leaked_str, "Hello, world!");
    /// #
    /// # // Clean up to avoid leak in test
    /// # unsafe { core::ptr::from_mut(leaked_str).drop_in_place() };
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let my_place = own!(String::from("Hello"));
    /// let ptr = Own::into_raw(my_place);
    /// unsafe {
    ///     let recovered = Own::from_raw(ptr);
    ///     assert_eq!(&*recovered, "Hello");
    /// }
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let my_place = own!(vec![1, 2, 3]);
    /// let ptr = Own::into_raw(my_place);
    /// let recovered: Own<Vec<i32>> = unsafe { Own::from_raw(ptr) };
    /// assert_eq!(&*recovered, &[1, 2, 3]);
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    /// use core::mem::MaybeUninit;
    ///
    /// let mut uninit_place = MaybeUninit::new(10);
    /// let owned_place: Own<i32> = unsafe { Own::from_mut(&mut uninit_place) };
    /// assert_eq!(*owned_place, 10);
    /// ```
    #[inline]
    pub unsafe fn from_mut(place: &'a mut impl Place<T>) -> Self {
        unsafe { Own::from_raw(place.as_mut_ptr()) }
    }

    /// Drops the value inside the place and converts it into an uninitialized
    /// reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let my_place = own!(String::from("Hello"));
    /// let uninit_place = Own::drop(my_place);
    /// // At this point, the String has been dropped.
    /// // We can now re-initialize the place.
    /// let my_place_again = uninit_place.write(String::from("World"));
    /// assert_eq!(&*my_place_again, "World");
    /// ```
    #[inline]
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
    /// use placid::prelude::*;
    ///
    /// let my_place: Own<i32> = own!(100);
    /// let (value, uninit_place): (i32, Uninit<i32>) = Own::take(my_place);
    /// assert_eq!(value, 100);
    /// // The place is now uninitialized, we can re-initialize it.
    /// let my_place_again: Own<i32> = uninit_place.write(200);
    /// assert_eq!(*my_place_again, 200);
    /// ```
    #[inline]
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
            /// use placid::prelude::*;
            /// use std::any::Any;
            ///
            #[doc = concat!("let value: Own<dyn ", stringify!($($t)*), "> = own!(42i32);")]
            /// match value.downcast::<i32>() {
            ///     Ok(owned) => assert_eq!(*owned, 42),
            ///     Err(_) => panic!("Downcast failed"),
            /// }
            /// ```
            #[inline]
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
            /// use placid::prelude::*;
            /// use std::any::Any;
            ///
            #[doc = concat!("let value: Own<dyn ", stringify!($($t)*), "> = own!(\"hello\");")]
            /// let downcast: Own<&str> = unsafe { value.downcast_unchecked() };
            /// ```
            #[inline]
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
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for Own<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized> fmt::Pointer for Own<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.inner, f)
    }
}

impl<'a, T: Clone> Own<'a, T> {
    /// Clones the value inside the owned reference into another place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let owned = placid::own!(String::from("Hello"));
    /// let mut another_place = core::mem::MaybeUninit::uninit();
    /// let cloned = owned.clone(&mut another_place);
    /// assert_eq!(&*cloned, "Hello");
    /// ```
    #[inline]
    pub fn clone<'b>(&self, to: &'b mut impl Place<T>) -> Own<'b, T> {
        to.write(|| (**self).clone())
    }
}

impl<'a, T: Default> Own<'a, T> {
    /// Initializes the place with the default value of `T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let mut place = core::mem::MaybeUninit::uninit();
    /// let owned: Own<Vec<i32>> = Own::default(&mut place);
    /// assert_eq!(&*owned, &[]);
    #[inline]
    pub fn default(place: &'a mut impl Place<T>) -> Self {
        place.write(T::default)
    }
}

impl<'a, T> Default for Own<'a, [T]> {
    #[inline]
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_mut(&mut [])) }
    }
}

impl<'a> Default for Own<'a, str> {
    #[inline]
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_ref("")) }
    }
}

impl<'a> Default for Own<'a, core::ffi::CStr> {
    #[inline]
    fn default() -> Self {
        unsafe { Own::from_inner(NonNull::from_ref(c"")) }
    }
}

impl<'a, 'b, T: ?Sized + PartialEq<U>, U: ?Sized> PartialEq<Own<'b, U>> for Own<'a, T> {
    #[inline]
    fn eq(&self, other: &Own<'b, U>) -> bool {
        **self == **other
    }
}

impl<'a, T: ?Sized + Eq> Eq for Own<'a, T> {}

impl<'a, 'b, T: ?Sized + PartialOrd<U>, U: ?Sized> PartialOrd<Own<'b, U>> for Own<'a, T> {
    #[inline]
    fn partial_cmp(&self, other: &Own<'b, U>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<'a, T: ?Sized + Ord> Ord for Own<'a, T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<'a, T: ?Sized + Hash> Hash for Own<'a, T> {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<'a, T: ?Sized + Hasher> Hasher for Own<'a, T> {
    #[inline]
    fn finish(&self) -> u64 {
        (**self).finish()
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes);
    }
}

impl<'a, T: ?Sized + Error> Error for Own<'a, T> {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        (**self).source()
    }
}

impl<'a, F: ?Sized + Future + Unpin> Future for Own<'a, F> {
    type Output = F::Output;

    #[inline]
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut **self).poll(cx)
    }
}

#[cfg(feature = "alloc")]
#[allow(dead_code)]
#[inline]
fn into_undrop_box<T: ?Sized>(own: Own<'_, T>) -> Box<T, impl Allocator> {
    use core::alloc::{AllocError, Allocator, Layout};

    let inner = own.inner;
    mem::forget(own);

    // SAFETY: Hack to call the function, moving out the possible DST from the
    // pointer. FIXME: Error-prone. Use a better way when available.
    unsafe {
        struct NullAlloc;

        unsafe impl Allocator for NullAlloc {
            fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
                Err(AllocError)
            }

            unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
                // No-op
            }
        }
        Box::from_raw_in(inner.as_ptr(), NullAlloc)
    }
}

impl<'a, I: ?Sized + Iterator> Iterator for Own<'a, I> {
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        (**self).next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        (**self).nth(n)
    }
}

#[cfg(feature = "fn-impl")]
mod fn_impl;

/// A trait for types that can be converted into owned places.
///
/// This trait allows for "extracting" an [owned] reference from various
/// container types that hold values. It is primarily used to facilitate the
/// creation of owned places from standard library containers like `Box`, `Rc`,
/// and `Arc`.
///
/// This trait is not meant to be used directly, as there is no such method as
/// `IntoOwn::into_own`, since the place itself should be converted. Instead,
/// callers of this trait can use the [`into_own!`] and [`into_pown!`] macros to
/// conveniently convert expressions into owned references.
///
/// # Safety
///
/// Implementors must ensure that `into_own_place` correctly converts the
/// container into a place that wraps the current contained value, i.e. the
/// place must be initialized with the value inside the container.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
/// use core::mem::MaybeUninit;
///
/// fn use_owned<T: IntoOwn>(value: T) -> T::Place {
///     let mut place: T::Place;
///     {
///         let owned = into_own!(place <- value);
///         // Use the owned reference...
///     }
///     place
/// }
///
/// let place: Box<MaybeUninit<i32>> = use_owned(Box::new(42));
/// // The place now can be re-initialized or used further.
/// ```
///
/// [owned]: crate::owned::Own
/// [`into_own!`]: crate::into_own!
/// [`into_pown!`]: crate::into_pown!
pub unsafe trait IntoOwn: Deref + Sized {
    /// The type of place associated with this container.
    type Place: Place<Self::Target, Init = Self>;

    /// Converts the container into its associated place wrapping the contained
    /// value.
    ///
    /// This method should not be used directly. Instead, use the [`into_own!`]
    /// macro.
    ///
    /// [`into_own!`]: crate::into_own!
    #[inline]
    fn into_own_place(self) -> Self::Place {
        Place::from_init(self)
    }
}

#[cfg(feature = "alloc")]
macro_rules! impl_std_alloc {
    (@IMP $ty:ident) => {
        unsafe impl<T, A: Allocator> IntoOwn for $ty<T, A> {
            type Place = $ty<MaybeUninit<T>, A>;
        }

        unsafe impl<T, A: Allocator> IntoOwn for $ty<[T], A> {
            type Place = $ty<[MaybeUninit<T>], A>;
        }

        unsafe impl<A: Allocator> IntoOwn for $ty<str, A> {
            type Place = $ty<[MaybeUninit<u8>], A>;
        }
    };
    ($($ty:ident),*) => {
        $(impl_std_alloc!(@IMP $ty);)*
    };
}

#[cfg(feature = "alloc")]
impl_std_alloc!(Box, Arc, Rc);

/// Creates an [owned reference] from a container, extracting the contained
/// value.
///
/// The macro converts the given expression into an owned place by extracting
/// the value inside the container. The resulting owned reference can be used
/// like any other owned reference.
///
/// For the pinned counterpart, see the [`into_pown!`] macro.
///
/// # Arguments
///
/// * `$e:expr` - An expression that evaluates to a container implementing the
///   `IntoOwn` trait.
/// * `$p:ident` - (optional) An identifier to bind the resulting place to. If
///   omitted, a temporary variable is created.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
/// let my_place: Own<i32> = into_own!(Box::new(55));
/// assert_eq!(*my_place, 55);
/// ```
///
/// ```rust
/// use placid::prelude::*;
/// use std::rc::Rc;
///
/// let mut place; // Rc<MaybeUninit<String>>
/// let owned = into_own!(place <- Rc::new(String::from("Hello")));
/// assert_eq!(&*owned, "Hello");
/// drop(owned);
///
/// let owned_again = place.write(String::from("World"));
/// assert_eq!(&*owned_again, "World");
/// ```
///
/// [owned reference]: crate::owned::Own
/// [`into_pown!`]: crate::into_pown!
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! into_own {
    ($p:ident <- $e:expr) => {{
        $p = $crate::owned::IntoOwn::into_own_place($e);
        unsafe { $crate::owned::Own::from_mut(&mut $p) }
    }};
    ($e:expr) => {{
        super let mut p;
        $crate::into_own!(p <- $e)
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

    #[cfg(feature = "alloc")]
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
