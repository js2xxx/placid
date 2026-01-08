use core::{convert::Infallible, marker::PhantomData};

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, IntoInit},
    pin::{DropSlot, POwn},
};

type PhantomResult<T, E> = PhantomData<(fn() -> T, fn() -> E)>;

pub struct TryRawPin<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<T: ?Sized, F, E> InitPin for TryRawPin<F, T, E>
where
    F: for<'a, 'b> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitPinError<'a, 'b, T, E>>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        (self.0)(place, slot)
    }
}

pub const fn try_raw_pin<T: ?Sized, E, F>(f: F) -> TryRawPin<F, T, E>
where
    F: for<'a, 'b> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, InitError<'a, T, E>>,
{
    TryRawPin(f, PhantomData)
}

impl<T: ?Sized, F, E> IntoInit<T, TryRawPin<F, T, E>> for F
where
    F: for<'a, 'b> FnOnce(
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

pub struct TryRaw<F, T: ?Sized, E>(F, PhantomResult<T, E>);

impl<T: ?Sized, F, E> InitPin for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a, 'b>(
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

impl<T: ?Sized, F, E> Init for TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        (self.0)(place)
    }
}

pub const fn try_raw<T, E, F>(f: F) -> TryRaw<F, T, E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    TryRaw(f, PhantomData)
}

impl<T: ?Sized, F, E> IntoInit<T, TryRaw<F, T, E>> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, InitError<'_, T, E>>,
{
    type Init = TryRaw<F, T, E>;
    type Error = E;

    fn into_init(self) -> Self::Init {
        TryRaw(self, PhantomData)
    }
}

pub struct RawPin<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<T: ?Sized, F> InitPin for RawPin<F, T>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        Ok((self.0)(place, slot))
    }
}

pub const fn raw_pin<T: ?Sized, F>(f: F) -> RawPin<F, T>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    RawPin(f, PhantomData)
}

impl<T: ?Sized, F> IntoInit<T, RawPin<F, T>> for F
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Init = RawPin<F, T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        RawPin(self, PhantomData)
    }
}

pub struct Raw<F, T: ?Sized>(F, PhantomData<fn() -> T>);

impl<T: ?Sized, F> InitPin for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        Ok(Own::into_pin((self.0)(place), slot))
    }
}

impl<T: ?Sized, F> Init for Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        Ok((self.0)(place))
    }
}

pub const fn raw<T: ?Sized, F>(f: F) -> Raw<F, T>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    Raw(f, PhantomData)
}

impl<T: ?Sized, F> IntoInit<T, Raw<F, T>> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Init = Raw<F, T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        Raw(self, PhantomData)
    }
}
