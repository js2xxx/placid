use core::{convert::Infallible, marker::PhantomData};

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, IntoInit},
    pin::{DropSlot, POwn},
};

type PhantomResult<T, E> = PhantomData<(fn() -> T, fn() -> E)>;

/// Initializes a place with a closure that has full control over the pinned
/// place.
///
/// This initializer is created from [`try_raw_pin()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TryRawPin<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<'b, T: ?Sized + 'b, F, E> InitPin<'b> for TryRawPin<F, T, E>
where
    F: for<'a> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitPinError<'a, 'b, T, E>>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
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
pub const fn try_raw_pin<'b, T: ?Sized + 'b, E, F>(f: F) -> TryRawPin<F, T, E>
where
    F: for<'a> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitPinError<'a, 'b, T, E>>,
{
    TryRawPin(f, PhantomData)
}

impl<'b, T: ?Sized + 'b, F, E> IntoInit<'b, T, TryRawPin<F, T, E>> for F
where
    F: for<'a> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitPinError<'a, 'b, T, E>>,
{
    type Init = TryRawPin<F, T, E>;
    type Error = E;

    fn into_init(self) -> Self::Init {
        TryRawPin(self, PhantomData)
    }
}

/// Initializes a place with a closure that has full control.
///
/// This initializer is created from [`try_raw()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TryRaw<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<'b, T: ?Sized, F, E> InitPin<'b> for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitPinError<'a, 'b, T, Self::Error>> {
        match (self.0)(place) {
            Ok(own) => Ok(Own::into_pin(own, slot)),
            Err(err) => Err(err.into_pin(slot)),
        }
    }
}

impl<'b, T: ?Sized, F, E> Init<'b> for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    fn init(self, place: Uninit<'b, T>) -> InitResult<'b, Self> {
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
pub const fn try_raw<T, E, F>(f: F) -> TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    TryRaw(f, PhantomData)
}

impl<'b, T: ?Sized, F, E> IntoInit<'b, T, TryRaw<F, T, E>> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    type Init = TryRaw<F, T, E>;
    type Error = E;

    fn into_init(self) -> Self::Init {
        TryRaw(self, PhantomData)
    }
}

/// Initializes a place with a closure that has full control over pinned
/// initialization.
///
/// This initializer is created from [`raw_pin()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RawPin<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<'b, T: ?Sized, F> InitPin<'b> for RawPin<F, T>
where
    F: for<'a> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
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
pub const fn raw_pin<'b, T: ?Sized, F>(f: F) -> RawPin<F, T>
where
    F: for<'a> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    RawPin(f, PhantomData)
}

impl<'b, T: ?Sized, F> IntoInit<'b, T, RawPin<F, T>> for F
where
    F: for<'a> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Init = RawPin<F, T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        RawPin(self, PhantomData)
    }
}

/// Initializes a place with a closure that has full control and cannot fail.
///
/// This initializer is created from [`raw()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Raw<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<'b, T: ?Sized, F> InitPin<'b> for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        Ok(Own::into_pin((self.0)(place), slot))
    }
}

impl<'b, T: ?Sized, F> Init<'b> for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
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
pub const fn raw<T: ?Sized, F>(f: F) -> Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    Raw(f, PhantomData)
}

impl<'b, T: ?Sized, F> IntoInit<'b, T, Raw<F, T>> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Init = Raw<F, T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        Raw(self, PhantomData)
    }
}
