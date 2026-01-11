//! Types and macros for managing pinned owned references with proper drop
//! semantics.
//!
//! This module provides utilities for creating [drop slots], which are used
//! to manage the lifetime of pinned owned references. The [`POwn<T>`] type
//! represents a pinned owned reference (semantically equivalent to
//! `Pin<Own<T>>`) that cannot be forgotten, ensuring that pinned values
//! are properly dropped. It also includes macros and traits for creating and
//! manipulating pinned owned references.
//!
//! For constructing pinned owned references onto the stack, see the
//! [`pown!`] macro.
//!
//! For converting containers into owned references, see the [`IntoOwn`] trait
//! and the [`into_pown!`] macro.
//!
//! [drop slots]: crate::drop_slot
//! [`POwn<T>`]: crate::pin::POwn
//! [`pown!`]: crate::pown
//! [`IntoOwn`]: crate::owned::IntoOwn
//! [`into_pown!`]: crate::into_pown

use core::{
    cell::Cell,
    error::Error,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::NonNull,
    task::{Context, Poll},
};

use crate::{owned::Own, place::Place, uninit::Uninit};

/// A slot that holds and manages the lifetime of a pinned owned value.
///
/// `DroppingSlot` is a container that ensures pinned values are properly
/// dropped, even if the pinned reference is somehow leaked or forgotten. It
/// manages the drop flag that tracks whether the value should be dropped when
/// the slot itself is dropped.
///
/// This struct is typically created implicitly through the [`drop_slot!`]
/// macro, which is the recommended way to create and manage drop slots.
///
/// [`drop_slot!`]: macro@crate::drop_slot
pub struct DroppingSlot<'a, T: ?Sized> {
    drop_flag: Cell<bool>,
    inner: MaybeUninit<Own<'a, T>>,
}

impl<'a, T: ?Sized> DroppingSlot<'a, T> {
    /// Creates a new `DroppingSlot`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::pin::DroppingSlot;
    ///
    /// let slot: DroppingSlot<String> = DroppingSlot::new();
    /// // Slot is now ready to be used with DropSlot::new_unchecked
    /// ```
    #[inline]
    pub const fn new() -> Self {
        DroppingSlot {
            drop_flag: Cell::new(true),
            inner: MaybeUninit::uninit(),
        }
    }

    fn assign(&mut self, own: Own<'a, T>) -> &Cell<bool> {
        if !self.drop_flag.replace(false) {
            // SAFETY: We are dropping the inner pinned value.
            unsafe { self.inner.assume_init_drop() };
        }
        self.inner.write(own);
        &self.drop_flag
    }
}

impl<'a, T: ?Sized> Default for DroppingSlot<'a, T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: ?Sized> Drop for DroppingSlot<'a, T> {
    fn drop(&mut self) {
        if !self.drop_flag.get() {
            // SAFETY: We are dropping the inner pinned value.
            unsafe { self.inner.assume_init_drop() }
        }
    }
}

/// A reference to a dropping slot that can be used to initialize pinned values.
///
/// `DropSlot` provides safe access to a `DroppingSlot` by borrowing it mutably.
/// It is used in conjunction with pinned initialization to ensure proper
/// cleanup of pinned values. The slot manages the drop flag that determines
/// whether the value should be dropped when the slot is destroyed.
///
/// This type is typically created through the [`drop_slot!`] macro, which
/// automatically handles the lifetime and safety requirements.
///
/// [`drop_slot!`]: macro@crate::drop_slot
pub struct DropSlot<'a, 'b, T: ?Sized>(&'b mut DroppingSlot<'a, T>);

impl<'a, 'b, T: ?Sized> fmt::Debug for DropSlot<'a, 'b, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DropSlot").finish()
    }
}

impl<'a, 'b, T: ?Sized> DropSlot<'a, 'b, T> {
    /// Creates a new `DropSlot` from an existing reference.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `DroppingSlot` won't be
    /// [`core::mem::forget`]ed. If the slot is forgotten, pinned values stored
    /// within it will not be properly dropped, leading to resource leaks and
    /// violations of pinning drop guarantees.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::pin::{DroppingSlot, DropSlot};
    ///
    /// let mut slot: DroppingSlot<i32> = DroppingSlot::new();
    /// let drop_slot: DropSlot<i32> = unsafe {
    ///     DropSlot::new_unchecked(&mut slot)
    /// };
    /// // Now drop_slot can be used to initialize pinned values
    /// ```
    #[inline]
    pub unsafe fn new_unchecked(slot: &'b mut DroppingSlot<'a, T>) -> Self {
        DropSlot(slot)
    }
}

/// Creates a new drop slot for pinned value initialization.
///
/// This macro is the recommended way to create a [`DropSlot`] constrained to
/// the current scope.
///
/// The macro ensures that the drop slot cannot be accidentally forgotten, as
/// the underlying drop slot is bound to the macro's scope and will be
/// automatically dropped when the scope ends.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let owned = own!(String::from("Hello"));
/// let drop_slot = placid::drop_slot!();
/// let pinned = Own::into_pin(owned, drop_slot);
/// assert_eq!(&*pinned, "Hello");
/// ```
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! drop_slot {
    () => {{
        super let mut slot = $crate::pin::DroppingSlot::new();
        unsafe { $crate::pin::DropSlot::new_unchecked(&mut slot) }
    }};
}

/// A [`Pin`]ned & [`Own`]ed reference.
///
/// This type semantically represents a `Pin<Own<'b, T>>`, but it is implemented
/// as a separate type. This is because `Pin<Own<'b, T>>` would allow being
/// [`mem::forget`]ed, which would lead to violations of the pinning guarantees.
/// See the dropping guarantee section in [`core::pin`] for more details.
///
/// `POwn` combines pinning with ownership, ensuring that:
/// - The value cannot be moved out of its memory location
/// - The value is guaranteed to be properly dropped
/// - The value cannot be forgotten (unlike regular `Pin<T>`)
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let pinned = pown!(vec![1, 2, 3]);
/// // The value is now pinned and cannot be moved
/// assert_eq!(*pinned, [1, 2, 3]);
/// // Even if we forget `pinned`, the value will still
/// // be properly dropped somewhere in `drop_slot`.
/// ```
pub struct POwn<'b, T: ?Sized> {
    drop_flag: &'b Cell<bool>,
    inner: NonNull<T>,
}

impl<'b, T: ?Sized> Unpin for POwn<'b, T> {}

impl<'b, T: ?Sized> Drop for POwn<'b, T> {
    fn drop(&mut self) {
        // Mark the value as dropped.
        self.drop_flag.set(true);
        // SAFETY: We are dropping the inner pinned value.
        unsafe { self.inner.drop_in_place() }
    }
}

/// Creates a new pinned place initialized with the given expression.
///
/// This macro allocates stack storage for the value and returns a pinned owned
/// reference to it.
///
/// # Examples
///
/// ```rust
/// let my_pinned_place = placid::pown!(String::from("Hello"));
/// assert_eq!(*my_pinned_place, "Hello");
/// ```
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! pown {
    ($e:expr) => {{
        super let mut place = ::core::mem::MaybeUninit::uninit();
        super let mut slot = $crate::pin::DroppingSlot::new();
        let drop_slot = unsafe { $crate::pin::DropSlot::new_unchecked(&mut slot) };
        $crate::place::Place::write_pin(&mut place, $e, drop_slot)
    }};
}

impl<'b, T: ?Sized> POwn<'b, T> {
    /// Creates a new `POwn` from a pinned owned reference and a drop flag.
    ///
    /// This method is typically called by methods like [`Own::into_pin`] rather
    /// than directly. It takes ownership of the value and stores it in the
    /// drop slot, ensuring that the drop flag can be used to track the
    /// value's lifetime.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let owned = own!(42i32);
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// // Pinned value is now created
    /// ```
    ///
    /// [`Own::into_pin`]: crate::owned::Own::into_pin
    pub fn new<'a>(own: Own<'a, T>, slot: DropSlot<'a, 'b, T>) -> Self {
        let inner = own.inner;
        let drop_flag = slot.0.assign(own);
        POwn { drop_flag, inner }
    }

    /// Gets a shared reference to the pinned value.
    ///
    /// This returns a `Pin<&T>` which ensures that the referenced value
    /// cannot be moved, even through shared references. This is safe because
    /// the value is stored in a pinned location.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let pinned = placid::pown!(String::from("pinned"));
    /// let pinned_ref = pinned.as_ref();
    /// assert_eq!(&*pinned_ref, "pinned");
    /// ```
    #[inline]
    pub const fn as_ref(&self) -> Pin<&T> {
        // SAFETY: `inner` is properly pinned.
        unsafe { Pin::new_unchecked(self.inner.as_ref()) }
    }

    /// Gets a mutable reference to the pinned value.
    ///
    /// This returns a `Pin<&mut T>` which ensures that the referenced value
    /// cannot be moved, even through mutable references. This is the pinned
    /// equivalent of a regular mutable reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut pinned = placid::pown!(vec![1, 2]);
    /// let mut pinned_mut = pinned.as_mut();
    /// pinned_mut.push(3);
    /// ```
    #[inline]
    pub const fn as_mut(&mut self) -> Pin<&mut T> {
        // SAFETY: `inner` is properly pinned.
        unsafe { Pin::new_unchecked(self.inner.as_mut()) }
    }

    /// Gets a [`Pin<&mut T>`] to the pinned value from the nested
    /// `Pin`-pointer.
    ///
    /// This method is useful when you have a `Pin<&mut POwn<T>>` and need to
    /// work with the pinned value directly. It unwraps the outer pin layer
    /// and provides access to the inner pinned mutable reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use core::pin::Pin;
    ///
    /// let mut pinned = placid::pown!(String::from("hello"));
    /// let pinned_mut: Pin<&mut String> = Pin::new(&mut pinned).as_deref_mut();
    /// // Now you can modify the string through the pinned reference
    /// ```
    #[inline]
    pub const fn as_deref_mut(self: Pin<&mut Self>) -> Pin<&mut T> {
        // SAFETY: `inner` is properly pinned.
        unsafe { Pin::new_unchecked(Pin::into_inner_unchecked(self).inner.as_mut()) }
    }

    /// Assigns a new value to the pinned place.
    ///
    /// This method replaces the current value with a new one, dropping the old
    /// value in the process. This is only available for sized types (`T:
    /// Sized`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut pinned = placid::pown!(42i32);
    /// pinned.set(100);
    /// assert_eq!(*pinned, 100);
    /// ```
    #[inline]
    pub fn set(&mut self, value: T)
    where
        T: Sized,
    {
        // SAFETY: `inner` is properly pinned.
        unsafe { *self.inner.as_ptr() = value }
    }

    /// Drops the pinned value inside the place and converts it into an
    /// uninitialized reference.
    ///
    /// This method consumes the pinned reference, drops the value, and returns
    /// an uninitialized reference to the same memory location. This allows you
    /// to re-initialize the place with a new value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let mut pinned = placid::pown!(String::from("hello"));
    /// let uninit = POwn::drop(pinned);
    /// // The String has been dropped, and we can re-initialize the place
    /// ```
    #[inline]
    pub fn drop(this: Self) -> Uninit<'b, T> {
        let inner = this.inner;
        drop(this);
        unsafe { Uninit::from_inner(inner) }
    }

    /// Converts the pinned owned reference into its unpinned variant.
    ///
    /// This method consumes the `POwn` and returns a regular `Own` reference.
    /// The method requires that `T: Unpin`, because unpinning an `!Unpin` type
    /// would violate pinning guarantees.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let mut pinned = placid::pown!(42i32); // i32 is Unpin
    /// let unpinned = POwn::into_inner(pinned);
    /// assert_eq!(*unpinned, 42);
    /// ```
    #[inline]
    pub fn into_inner(this: Self) -> Own<'b, T>
    where
        T: Unpin,
    {
        let inner = this.inner;
        this.drop_flag.set(true);
        mem::forget(this);
        unsafe { Own::from_inner(inner) }
    }
}

impl<'b, T: ?Sized> Deref for POwn<'b, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.inner.as_ref() }
    }
}

impl<'b, T: ?Sized + Unpin> DerefMut for POwn<'b, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.inner.as_mut() }
    }
}

impl<'b, T: ?Sized + fmt::Debug> fmt::Debug for POwn<'b, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'b, T: ?Sized + fmt::Display> fmt::Display for POwn<'b, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized> fmt::Pointer for POwn<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.inner, f)
    }
}

impl<'a, T: Clone> POwn<'a, T> {
    /// Clones the value inside the pinned owned reference into another place.
    ///
    /// This method creates a new pinned owned reference by cloning the value
    /// from the current pinned reference into the specified place. The new
    /// value is properly pinned in the target location.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let pinned = placid::pown!(String::from("hello"));
    /// let mut place = core::mem::MaybeUninit::uninit();
    /// let drop_slot = placid::drop_slot!();
    /// let cloned: POwn<String> = pinned.clone(&mut place, drop_slot);
    /// assert_eq!(&*cloned, "hello");
    /// ```
    #[inline]
    pub fn clone<'p, 'b>(
        &self,
        to: &'p mut impl Place<T>,
        slot: DropSlot<'p, 'b, T>,
    ) -> POwn<'b, T> {
        to.write_pin(|| (**self).clone(), slot)
    }
}

impl<'b, T: Default> POwn<'b, T> {
    /// Initializes the place with the default value of `T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let mut place = core::mem::MaybeUninit::uninit();
    /// let drop_slot = placid::drop_slot!();
    /// let owned: POwn<Vec<i32>> = POwn::default(&mut place, drop_slot);
    /// assert_eq!(&*owned, &[]);
    /// ```
    #[inline]
    pub fn default<'a>(place: &'a mut impl Place<T>, slot: DropSlot<'a, 'b, T>) -> Self {
        place.write_pin(T::default, slot)
    }
}

impl<'a, 'b, T: ?Sized + PartialEq<U>, U: ?Sized> PartialEq<POwn<'b, U>> for POwn<'a, T> {
    #[inline]
    fn eq(&self, other: &POwn<'b, U>) -> bool {
        **self == **other
    }
}

impl<'a, T: ?Sized + Eq> Eq for POwn<'a, T> {}

impl<'a, 'b, T: ?Sized + PartialOrd<U>, U: ?Sized> PartialOrd<POwn<'b, U>> for POwn<'a, T> {
    #[inline]
    fn partial_cmp(&self, other: &POwn<'b, U>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<'a, T: ?Sized + Ord> Ord for POwn<'a, T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<'a, T: ?Sized + Hash> Hash for POwn<'a, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<'a, T: ?Sized + Hasher + Unpin> Hasher for POwn<'a, T> {
    #[inline]
    fn finish(&self) -> u64 {
        (**self).finish()
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes);
    }
}

impl<'a, T: ?Sized + Error> Error for POwn<'a, T> {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        (**self).source()
    }
}

impl<'a, F: ?Sized + Future> Future for POwn<'a, F> {
    type Output = F::Output;

    #[inline]
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.as_deref_mut().poll(cx)
    }
}

/// Creates a new [pinned owned reference] initialized with the given
/// expression.
///
/// The macro converts the given expression into a pinned owned place by
/// extracting the value inside the container. The resulting pinned owned
/// reference can be used like any other owned reference.
///
/// For the unpinned counterpart, see [`into_own!`].
///
/// # Arguments
///
/// * `$e:expr` - An expression that evaluates to a container implementing the
///   [`IntoOwn`] trait.
/// * `$p:ident` - (optional) An identifier to bind the resulting place to. If
///   omitted, a temporary variable is created.
/// * `$slot:ident` - (optional) An identifier to bind the drop slot to. If
///   omitted, a temporary drop slot is created.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let pown = into_pown!(Box::pin(100u32));
/// assert_eq!(*pown, 100);
/// ```
///
/// ```rust
/// use placid::prelude::*;
/// use std::rc::Rc;
///
/// let mut place;
/// {
///     let pown = into_pown!(place <- Rc::pin(200));
///     assert_eq!(*pown, 200);
///
///     // `drop(pown)` alone is not enough to end the borrow of `place`,
///     // because an implicit `DropSlot` is still holding a reference to it,
///     // ensuring proper drop semantics if `pown` get `mem::forget`ed. Thus,
///     // we need a brace scope here.
/// }
/// let reuse = place.write(300);
/// assert_eq!(*reuse, 300);
/// ```
///
/// [pinned owned reference]: crate::pin::POwn
/// [`into_own!`]: crate::into_own!
/// [`IntoOwn`]: crate::owned::IntoOwn
#[macro_export]
#[allow_internal_unstable(super_let)]
macro_rules! into_pown {
    ($p:ident, $slot:ident <- $e:expr) => {{
        use ::core::pin::Pin;

        let pinned = $e;
        let init = unsafe { Pin::into_inner_unchecked(pinned) };
        $p = $crate::owned::IntoOwn::into_own_place(init);
        unsafe { $crate::owned::Own::into_pin($crate::owned::Own::from_mut(&mut $p), $slot) }
    }};
    ($p:ident <- $e:expr) => {{
        use ::core::pin::Pin;

        super let mut slot = $crate::pin::DroppingSlot::new();
        let slot = unsafe { $crate::pin::DropSlot::new_unchecked(&mut slot) };

        let pinned = $e;
        let init = unsafe { Pin::into_inner_unchecked(pinned) };
        $p = $crate::owned::IntoOwn::into_own_place(init);
        unsafe { $crate::owned::Own::into_pin($crate::owned::Own::from_mut(&mut $p), slot) }
    }};
    ($e:expr) => {{
        super let mut p;
        $crate::into_pown!(p <- $e)
    }};
}

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
    use alloc::boxed::Box;

    use super::*;

    #[test]
    fn test_into_pown() {
        let mut my_place;
        {
            let owned = into_pown!(my_place <- Box::pin(55));
            assert_eq!(*owned, 55);
        }
        my_place.write(123);

        let owned2 = into_pown!(Box::pin(77));
        assert_eq!(*owned2, 77);
    }
}
