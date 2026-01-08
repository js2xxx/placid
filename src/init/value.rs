use core::convert::Infallible;

use crate::{
    Own, Uninit,
    init::{Error, Init, InitPin},
    pin::{DropSlot, POwn},
};

pub enum FromValue {}

impl<T> InitPin<T, FromValue> for T {
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        (*place).write(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T> Init<T, FromValue> for T {
    fn init(self, mut place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        (*place).write(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn of<T>(value: T) -> impl Init<T, FromValue, Error = Infallible> {
    value
}

pub enum TryFromFn {}

impl<T, F, E> InitPin<T, TryFromFn> for F
where
    F: FnOnce() -> Result<T, E>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: crate::pin::DropSlot<'a, 'b, T>,
    ) -> Result<crate::pin::POwn<'b, T>, Error<'a, T, Self::Error>> {
        match self() {
            Ok(value) => Ok(place.write_pin(value, slot)),
            Err(e) => Err(Error { error: e, place }),
        }
    }
}

impl<T, F, E> Init<T, TryFromFn> for F
where
    F: FnOnce() -> Result<T, E>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        match self() {
            Ok(value) => Ok(place.write(value)),
            Err(e) => Err(Error { error: e, place }),
        }
    }
}

pub const fn try_with<T, F, E>(f: F) -> impl Init<T, TryFromFn, Error = E>
where
    F: FnOnce() -> Result<T, E>,
{
    f
}

pub enum FromFn {}

impl<T, F> InitPin<T, FromFn> for F
where
    F: FnOnce() -> T,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        place.try_write_pin(self(), slot)
    }
}

impl<T, F> Init<T, FromFn> for F
where
    F: FnOnce() -> T,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        place.try_write(self())
    }
}

pub const fn with<T, F>(f: F) -> impl Init<T, FromFn, Error = Infallible>
where
    F: FnOnce() -> T,
{
    f
}
