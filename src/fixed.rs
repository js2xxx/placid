//! Types that make data fixed to a location for an amount of time.
//!
//! See the [`Fix`] type for more details.

#[cfg(feature = "alloc")]
use core::alloc::Allocator;
use core::{
    cmp, fmt,
    hash::{Hash, Hasher},
    mem::ManuallyDrop,
    ops::{CoerceUnsized, Deref, DerefMut, DispatchFromDyn},
};

use crate::{
    owned::{IntoOwn, MoveToUninit, Own},
    pin::{DropSlot, POwn},
    place::{FromPlaceMut, Place},
    sealed,
    uninit::Uninit,
};

/// A type that wraps a pointer and makes the underlying data unmovable.
///
/// `Fix` is a wrapper type that can be used to make the target data inside a
/// pointer unmovable for its associated lifetime.
///
/// This type is extremely similar to the `Pin` type in the standard library,
/// but it has *one less requirement*: **the target type does not need to remain
/// valid at its memory location until it is dropped**. In other words, the
/// requirement drop enables 2 safe operations:
///
/// 1. The fixed data can be **safely leaked/forgotten** without causing
///    undefined behavior;
/// 2. The fixation is **temporary**, which means that a `Fix<&mut T>` can be
///    safely constructed from a `&mut T`.
///
/// Another difference is that `Fix` does not customize `Fix`-projections as
/// `Pin` does. Instead, the projection is automatically implemented & supported
/// for all structural operations via the [`munge`] crate.
///
/// # Undo the behavior
///
/// Similar to `Unpin` as the opt-out trait for `Pin`, the [`MoveToUninit`]
/// trait is the opt-out trait for `Fix`. If the target type of a `Fix` pointer
/// implements `MoveToUninit`, then the target data can be safely moved out of
/// the pointer.
///
/// Nevertheless, unlike `Unpin`, types that implement `MoveToUninit` do not
/// ensure a byte-wise move, which is encoded in the `IS_TRIVIAL` associated
/// constant. For types that are not trivially movable, the
/// [`MoveToUninit::move_to`] method must be used to move the data out of
/// the pointer.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Fix<P> {
    pointer: P,
}

impl<P: sealed::Sealed> sealed::Sealed for Fix<P> {}

impl<'a, P: FromPlaceMut<'a>> FromPlaceMut<'a> for Fix<P> {
    #[inline]
    unsafe fn from_place_mut(place: &'a mut impl Place<P::Target>) -> Self {
        Self {
            pointer: unsafe { P::from_place_mut(place) },
        }
    }
}

impl<P: Deref, Q: Deref> PartialEq<Fix<Q>> for Fix<P>
where
    P::Target: PartialEq<Q::Target>,
{
    #[inline]
    fn eq(&self, other: &Fix<Q>) -> bool {
        P::Target::eq(self, other)
    }

    #[expect(clippy::partialeq_ne_impl)]
    #[inline]
    fn ne(&self, other: &Fix<Q>) -> bool {
        P::Target::ne(self, other)
    }
}

impl<P: Deref<Target: Eq + PartialEq>> Eq for Fix<P> {}

impl<P: Deref, Q: Deref> PartialOrd<Fix<Q>> for Fix<P>
where
    P::Target: PartialOrd<Q::Target>,
{
    #[inline]
    fn partial_cmp(&self, other: &Fix<Q>) -> Option<cmp::Ordering> {
        P::Target::partial_cmp(self, other)
    }

    #[inline]
    fn lt(&self, other: &Fix<Q>) -> bool {
        P::Target::lt(self, other)
    }

    #[inline]
    fn le(&self, other: &Fix<Q>) -> bool {
        P::Target::le(self, other)
    }

    #[inline]
    fn gt(&self, other: &Fix<Q>) -> bool {
        P::Target::gt(self, other)
    }

    #[inline]
    fn ge(&self, other: &Fix<Q>) -> bool {
        P::Target::ge(self, other)
    }
}

impl<P: Deref<Target: Ord>> Ord for Fix<P> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        P::Target::cmp(self, other)
    }
}

impl<P: Deref<Target: Hash>> Hash for Fix<P> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        P::Target::hash(self, state);
    }
}

impl<P: Deref<Target: MoveToUninit>> Fix<P> {
    /// Unwraps the underlying pointer and returns it.
    ///
    /// Doing this operation safely requires that the data pointed at by this
    /// pointer is trivially movable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::fixed::Fix;
    ///
    /// let mut value = 42;
    /// let x = Fix::new(&mut value);
    /// let y = Fix::into_inner(x);
    /// assert_eq!(y, &mut 42);
    /// ```
    #[inline]
    pub fn into_inner(this: Self) -> P {
        assert_trivially_movable!(P::Target);
        // SAFETY: `T` is trivially movable, so it is safe unwrapping the pointer.
        unsafe { Self::into_inner_unchecked(this) }
    }
}

impl<P: Deref> Fix<P> {
    /// Constructs a new `Fix`ed pointer.
    ///
    /// This function is safe because fixation is temporary.
    #[inline]
    pub const fn new(pointer: P) -> Self {
        Self { pointer }
    }

    /// Unwraps the underlying pointer and returns it.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the data pointed at by this pointer is not
    /// moved during the lifetime of this pointer.
    ///
    /// If the underlying pointer is movable, the safe variant should be used
    /// instead.
    #[inline]
    pub unsafe fn into_inner_unchecked(this: Self) -> P {
        // SAFETY: `Self` does not implement `Drop`, so it is safe to read the pointer
        // without dropping it.
        unsafe { core::ptr::read(&ManuallyDrop::new(this).pointer) }
    }

    /// Gets a shared reference to the fixed data.
    #[inline]
    pub fn as_ref(&self) -> Fix<&P::Target>
    where
        P: Deref,
    {
        Fix::new(&self.pointer)
    }
}

impl<P: DerefMut> Fix<P> {
    /// Gets a mutable reference to the fixed data.
    #[inline]
    pub fn as_mut(&mut self) -> Fix<&mut P::Target>
    where
        P: DerefMut,
    {
        Fix::new(&mut self.pointer)
    }

    /// Gets a mutable reference to the fixed data from the nested `Fix`
    /// pointer.
    ///
    /// This method is safe because `Fix` is idempotent, so the outer pointer
    /// can be safely unwrapped without violating the fixation of the inner
    /// pointer.
    #[inline]
    pub fn as_deref_mut(self: Fix<&mut Self>) -> Fix<&mut P::Target>
    where
        P: DerefMut,
    {
        // SAFETY: `Fix` is idempotent, so it is safe to unwrap the outer pointer.
        unsafe { self.get_unchecked_mut() }.as_mut()
    }
}

impl<'a, T: ?Sized> Fix<&'a T> {
    /// Gets a shared reference out of the fixed pointer.
    ///
    /// This method is safe because a shared reference does not allow moving the
    /// data.
    #[inline]
    pub const fn get_ref(self) -> &'a T {
        self.pointer
    }
}

impl<'a, T: ?Sized> Fix<&'a mut T> {
    /// Converts this `Fix<&mut T>` into a `Fix<&T>` with the same lifetime.
    #[inline]
    pub const fn into_ref(self) -> Fix<&'a T> {
        Fix::new(self.pointer)
    }

    /// Gets a mutable reference out of the fixed pointer.
    ///
    /// This requires that the data pointed at by this pointer is trivially
    /// movable, because otherwise it would be possible to move the data out of
    /// the pointer and violate the fixation.
    #[inline]
    pub const fn get_mut(self) -> &'a mut T
    where
        T: MoveToUninit,
    {
        assert_trivially_movable!(T);
        self.pointer
    }

    /// Gets a mutable reference out of the fixed pointer without checking the
    /// movability of the target type.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the data pointed at by this pointer is
    /// not moved during lifetime `'a`. If the underlying pointer is trivially
    /// movable, [the safe variant] should be used instead.
    ///
    /// [the safe variant]: Self::get_mut
    #[inline]
    pub const unsafe fn get_unchecked_mut(self) -> &'a mut T {
        self.pointer
    }
}

impl<'a, T: ?Sized> Fix<Own<'a, T>> {
    /// Moves the data out of this `Fix<Own<T>>` and into the given `Uninit`.
    ///
    /// This requires that the target type of this pointer implements
    /// `MoveToUninit`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::prelude::*;
    ///
    /// let own = own!(String::from("hello"));
    /// let fix = Fix::new(own);
    /// let uninit = uninit!();
    /// let fix = fix.move_to(uninit);
    /// assert_eq!(&*fix, "hello");
    /// ```
    #[inline]
    pub fn move_to<'d>(self, to: Uninit<'d, T>) -> Fix<Own<'d, T>>
    where
        T: MoveToUninit,
    {
        T::move_to(self, to)
    }

    /// Converts the fixed owned reference into a pinned owned reference.
    ///
    /// If the value inside the place is not `!Unpin`, this ensures that it
    /// cannot be moved out of the place.
    #[inline]
    pub fn into_pin<'b>(this: impl Into<Self>, drop_slot: DropSlot<'a, 'b, T>) -> POwn<'b, T> {
        // SAFETY: We don't move the data out of the place.
        Own::into_pin(unsafe { Fix::into_inner_unchecked(this.into()) }, drop_slot)
    }
}

impl<P: Deref> Deref for Fix<P> {
    type Target = P::Target;

    #[inline]
    fn deref(&self) -> &P::Target {
        &self.pointer
    }
}

impl<P: DerefMut<Target: MoveToUninit>> DerefMut for Fix<P> {
    #[inline]
    fn deref_mut(&mut self) -> &mut P::Target {
        assert_trivially_movable!(P::Target);
        &mut self.pointer
    }
}

unsafe impl<P: munge::Destructure> munge::Destructure for Fix<P> {
    type Destructuring = P::Destructuring;
    type Underlying = P::Underlying;

    fn underlying(&mut self) -> *mut Self::Underlying {
        self.pointer.underlying()
    }
}

unsafe impl<T, P> munge::Restructure<T> for Fix<P>
where
    T: ?Sized,
    P: munge::Restructure<T, Restructured: Deref>,
{
    type Restructured = Fix<P::Restructured>;

    unsafe fn restructure(&self, ptr: *mut T) -> Self::Restructured {
        Fix::new(unsafe { self.pointer.restructure(ptr) })
    }
}

impl<P: fmt::Debug> fmt::Debug for Fix<P> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        P::fmt(&self.pointer, f)
    }
}

impl<P: fmt::Display> fmt::Display for Fix<P> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        P::fmt(&self.pointer, f)
    }
}

impl<P: fmt::Pointer> fmt::Pointer for Fix<P> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        P::fmt(&self.pointer, f)
    }
}

impl<P, U> CoerceUnsized<Fix<U>> for Fix<P>
where
    P: CoerceUnsized<U> + FixCoerceUnsized,
    U: FixCoerceUnsized,
{
}

impl<P, U> DispatchFromDyn<Fix<U>> for Fix<P>
where
    P: DispatchFromDyn<U> + FixCoerceUnsized,
    U: FixCoerceUnsized,
{
}

impl<P: Deref> From<P> for Fix<P> {
    #[inline]
    fn from(own: P) -> Self {
        Fix::new(own)
    }
}

unsafe impl<P: IntoOwn> IntoOwn for Fix<P> {
    type Place = P::Place;
    type IntoOwn<'a, T: ?Sized + 'a> = Fix<P::IntoOwn<'a, T>>;

    fn into_own_place(self) -> Self::Place {
        // SAFETY: The value validity of `self` is hidden behind `Self::Place`, so it is
        // safe to unwrap the pointer without dropping it.
        unsafe { Fix::into_inner_unchecked(self).into_own_place() }
    }
}

impl<'t, T> Fix<&'t Option<T>> {
    /// Converts this `Fix<&Option<T>>` into a `Fix<&Option<T>>`.
    pub const fn as_fix_ref(self) -> Option<Fix<&'t T>> {
        match self.pointer {
            Some(x) => Some(Fix::new(x)),
            None => None,
        }
    }
}

impl<'t, T> Fix<&'t mut Option<T>> {
    /// Converts this `Fix<&mut Option<T>>` into a `Fix<&mut Option<T>>`.
    pub const fn as_fix_mut(self) -> Option<Fix<&'t mut T>> {
        match self.pointer {
            Some(x) => Some(Fix::new(x)),
            None => None,
        }
    }
}

/// A marker trait for types that can be safely coerced to unsized types in
/// `Fix`.
///
/// This trait is the equivalent of [`PinCoerceUnsized`] for `Pin`. The safety
/// requirements are currently the same as those of `PinCoerceUnsized`, but they
/// may be relaxed in the future.
///
/// # Safety
///
/// Given a pointer of this type, the concrete type returned by its `deref`
/// method and (if it implements `DerefMut`) its `deref_mut` method must be the
/// same type and must not change without a modification. The following
/// operations are not considered modifications:
///
/// * Moving the pointer.
/// * Performing unsizing coercions on the pointer.
/// * Performing dynamic dispatch with the pointer.
/// * Calling `deref` or `deref_mut` on the pointer.
///
/// The concrete type of a trait object is the type that the vtable corresponds
/// to. The concrete type of a slice is an array of the same element type and
/// the length specified in the metadata. The concrete type of a sized type
/// is the type itself.
///
/// [`PinCoerceUnsized`]: core::pin::PinCoerceUnsized
pub unsafe trait FixCoerceUnsized {}

unsafe impl<'a, T: ?Sized> FixCoerceUnsized for Own<'a, T> {}

unsafe impl<T: ?Sized> FixCoerceUnsized for &T {}
unsafe impl<T: ?Sized> FixCoerceUnsized for &mut T {}
unsafe impl<T: ?Sized> FixCoerceUnsized for core::cell::Ref<'_, T> {}
unsafe impl<T: ?Sized> FixCoerceUnsized for core::cell::RefMut<'_, T> {}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized, A: Allocator> FixCoerceUnsized for alloc::boxed::Box<T, A> {}
#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized, A: Allocator> FixCoerceUnsized for alloc::rc::Rc<T, A> {}
#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized, A: Allocator> FixCoerceUnsized for alloc::sync::Arc<T, A> {}
