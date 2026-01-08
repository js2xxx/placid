use core::convert::Infallible;

use crate::{
    Own, Uninit,
    init::{Error, Init, InitPin},
    pin::{DropSlot, POwn},
};

pub enum TryFromRawPin {}

impl<T: ?Sized, F, E> InitPin<T, TryFromRawPin> for F
where
    F: for<'a, 'b> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, E>>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        self(place, slot)
    }
}

pub const fn try_raw_pin<T, F, E>(f: F) -> impl InitPin<T, TryFromRawPin, Error = E>
where
    F: for<'a, 'b> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, E>>,
{
    f
}

pub enum TryFromRaw {}

impl<T: ?Sized, F, E> InitPin<T, TryFromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, E>>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        self(place).map(|own| Own::into_pin(own, slot))
    }
}

impl<T: ?Sized, F, E> Init<T, TryFromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, E>>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        self(place)
    }
}

pub const fn try_raw<T, F, E>(f: F) -> impl Init<T, TryFromRaw, Error = E>
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, E>>,
{
    f
}

pub enum FromRawPin {}

impl<T: ?Sized, F> InitPin<T, FromRawPin> for F
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        Ok(self(place, slot))
    }
}

pub const fn raw_pin<T, F>(f: F) -> impl InitPin<T, FromRawPin, Error = Infallible>
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    f
}

pub enum FromRaw {}

impl<T: ?Sized, F> InitPin<T, FromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        Ok(Own::into_pin(self(place), slot))
    }
}

impl<T: ?Sized, F> Init<T, FromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        Ok(self(place))
    }
}

pub const fn raw<T, F>(f: F) -> impl Init<T, FromRaw, Error = Infallible>
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    f
}
