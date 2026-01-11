use core::{convert::Infallible, marker::PhantomData};

use crate::{
    init::{Init, InitPin, InitPinResult, InitResult, Initializer},
    owned::Own,
    pin::{DropSlot, POwn},
    uninit::Uninit,
};

type PhantomResult<T, E> = PhantomData<(fn() -> T, fn() -> E)>;

/// Initializes a place with a closure that has full control over the pinned
/// place.
///
/// This initializer is created from [`try_raw_pin()`] factory function.
#[derive(Debug, PartialEq)]
pub struct TryRawPin<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<T: ?Sized, F, E> Initializer for TryRawPin<F, T, E> {
    type Error = E;
}

impl<T: ?Sized, F, E> InitPin<T> for TryRawPin<F, T, E>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> InitPinResult<'a, 'b, T, E>,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, E> {
        (self.0)(place, slot)
    }
}

/// Creates a raw initializer from a closure.
///
/// This is the most low-level initializer for pinned initialization. It
/// provides the closure with complete access to both the uninitialized place
/// and the drop slot, allowing maximum flexibility for complex initialization
/// patterns. The closure can fail by returning an error.
///
/// This is rarely needed for typical use cases and is primarily useful for
/// implementing custom initializers or library-level primitives.
#[inline]
pub const fn try_raw_pin<T: ?Sized, E, F>(f: F) -> TryRawPin<F, T, E>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> InitPinResult<'a, 'b, T, E>,
{
    TryRawPin(f, PhantomData)
}

/// Initializes a place with a closure that has full control.
///
/// This initializer is created from [`try_raw()`] factory function.
#[derive(Debug, PartialEq)]
pub struct TryRaw<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<T: ?Sized, F, E> Initializer for TryRaw<F, T, E> {
    type Error = E;
}

impl<T: ?Sized, F, E> InitPin<T> for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> InitResult<'_, T, E>,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, E> {
        match (self.0)(place) {
            Ok(own) => Ok(Own::into_pin(own, slot)),
            Err(err) => Err(err.into_pin(slot)),
        }
    }
}

impl<T: ?Sized, F, E> Init<T> for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> InitResult<'_, T, E>,
{
    #[inline]
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, E> {
        (self.0)(place)
    }
}

/// Creates a raw initializer from a closure.
///
/// This is a low-level initializer for non-pinned initialization. It
/// provides the closure with complete access to the uninitialized place,
/// allowing it to implement custom initialization logic. The closure can fail
/// by returning an error.
///
/// This is rarely needed for typical use cases and is primarily useful for
/// implementing custom initializers or library-level primitives.
#[inline]
pub const fn try_raw<T, E, F>(f: F) -> TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> InitResult<'_, T, E>,
{
    TryRaw(f, PhantomData)
}

/// Initializes a place with a closure that has full control over pinned
/// initialization.
///
/// This initializer is created from [`raw_pin()`] factory function.
#[derive(Debug, PartialEq)]
pub struct RawPin<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<T: ?Sized, F> Initializer for RawPin<F, T> {
    type Error = Infallible;
}

impl<T: ?Sized, F> InitPin<T> for RawPin<F, T>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        Ok((self.0)(place, slot))
    }
}

/// Creates a raw pinned initializer from a closure.
///
/// This is similar to [`try_raw_pin`] but for infallible initialization. The
/// closure has complete control over the pinned place and drop slot, and cannot
/// fail.
///
/// This is primarily useful for implementing custom initializers that combine
/// the flexibility of raw access with pinned semantics.
#[inline]
pub const fn raw_pin<T: ?Sized, F>(f: F) -> RawPin<F, T>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    RawPin(f, PhantomData)
}

/// Initializes a place with a closure that has full control and cannot fail.
///
/// This initializer is created from [`raw()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Raw<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<T: ?Sized, F> Initializer for Raw<F, T> {
    type Error = Infallible;
}

impl<T: ?Sized, F> InitPin<T> for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        Ok(Own::into_pin((self.0)(place), slot))
    }
}

impl<T: ?Sized, F> Init<T> for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    #[inline]
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, Infallible> {
        Ok((self.0)(place))
    }
}

/// Creates a raw initializer from a closure.
///
/// This is similar to [`try_raw`] but for infallible initialization. The
/// closure has complete control over the uninitialized place and cannot fail.
///
/// This is primarily useful for implementing custom initializers that combine
/// the flexibility of raw access with infallible semantics.
#[inline]
pub const fn raw<T: ?Sized, F>(f: F) -> Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    Raw(f, PhantomData)
}
