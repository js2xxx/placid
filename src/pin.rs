use core::{
    cell::Cell,
    fmt,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::NonNull,
};

use crate::{Own, Uninit};

/// A slot that holds and manages the lifetime of a pinned owned value.
///
/// `DroppingSlot` is a container that ensures pinned values are properly
/// dropped, even if the pinned reference is somehow leaked or forgotten. It
/// manages the drop flag that tracks whether the value should be dropped when
/// the slot itself is dropped.
///
/// This struct is typically created implicitly through the [`drop_slot!`]
/// macro, which is the recommended way to create and manage drop slots.
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
    pub unsafe fn new_unchecked(slot: &'b mut DroppingSlot<'a, T>) -> Self {
        DropSlot(slot)
    }
}

/// Creates a new drop slot for pinned value initialization.
///
/// This macro is the recommended way to create a `DropSlot`. It automatically
/// creates a `DroppingSlot` with the appropriate scope and returns a `DropSlot`
/// reference that can be used to initialize pinned values.
///
/// The macro ensures that the drop slot cannot be accidentally forgotten, as
/// the underlying `DroppingSlot` is bound to the macro's scope and will be
/// automatically dropped when the scope ends.
///
/// # Examples
///
/// ```rust
/// use placid::{place, Own};
///
/// let owned = place!(String::from("Hello"));
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
/// use placid::{place, Own};
///
/// let owned = place!(vec![1, 2, 3]);
/// let drop_slot = placid::drop_slot!();
/// let mut pinned = Own::into_pin(owned, drop_slot);
/// // The value is now pinned and cannot be moved
/// assert_eq!(*pinned, vec![1, 2, 3]);
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
    /// use placid::{place, Own};
    /// use placid::pin::{DroppingSlot, DropSlot};
    ///
    /// let owned = place!(42i32);
    /// let mut slot = DroppingSlot::new();
    /// let drop_slot = unsafe { DropSlot::new_unchecked(&mut slot) };
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// // Pinned value is now created
    /// ```
    ///
    /// [`Own::into_pin`]: crate::Own::into_pin
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
    /// use placid::{place, Own};
    ///
    /// let owned = place!(String::from("pinned"));
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// let pinned_ref = pinned.as_ref();
    /// assert_eq!(&*pinned_ref, "pinned");
    /// ```
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
    /// use placid::{place, Own};
    ///
    /// let owned = place!(vec![1, 2]);
    /// let drop_slot = placid::drop_slot!();
    /// let mut pinned = Own::into_pin(owned, drop_slot);
    /// let mut pinned_mut = pinned.as_mut();
    /// pinned_mut.push(3);
    /// ```
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
    /// use placid::{place, Own};
    ///
    /// let owned = place!(String::from("hello"));
    /// let drop_slot = placid::drop_slot!();
    /// let mut pinned = Own::into_pin(owned, drop_slot);
    /// let pinned_mut: Pin<&mut String> = Pin::new(&mut pinned).as_deref_mut();
    /// // Now you can modify the string through the pinned reference
    /// ```
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
    /// use placid::{place, Own};
    ///
    /// let owned = place!(42i32);
    /// let drop_slot = placid::drop_slot!();
    /// let mut pinned = Own::into_pin(owned, drop_slot);
    /// pinned.set(100);
    /// assert_eq!(*pinned, 100);
    /// ```
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
    /// use placid::{place, Own};
    /// use placid::pin::POwn;
    ///
    /// let owned = place!(String::from("hello"));
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// let uninit = POwn::drop(pinned);
    /// // The String has been dropped, and we can re-initialize the place
    /// ```
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
    /// use placid::{place, Own};
    /// use placid::pin::POwn;
    ///
    /// let owned = place!(42i32); // i32 is Unpin
    /// let drop_slot = placid::drop_slot!();
    /// let pinned = Own::into_pin(owned, drop_slot);
    /// let unpinned = POwn::into_inner(pinned);
    /// assert_eq!(*unpinned, 42);
    /// ```
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

    fn deref(&self) -> &Self::Target {
        unsafe { self.inner.as_ref() }
    }
}

impl<'b, T: ?Sized + Unpin> DerefMut for POwn<'b, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.inner.as_mut() }
    }
}

impl<'b, T: ?Sized + fmt::Debug> fmt::Debug for POwn<'b, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'b, T: ?Sized + fmt::Display> fmt::Display for POwn<'b, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}
