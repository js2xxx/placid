use core::convert::Infallible;

use crate::{
    Uninit,
    init::{Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, IntoInit},
    pin::DropSlot,
};

pub struct Value<T>(T);

impl<T> InitPin for Value<T> {
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        (*place).write(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T> Init for Value<T> {
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, Self> {
        (*place).write(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn value<T>(value: T) -> Value<T> {
    Value(value)
}

impl<T> IntoInit<T, Value<T>> for T {
    type Init = Value<T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        Value(self)
    }
}

pub struct TryWith<F>(F);

impl<T, E, F> InitPin for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        match (self.0)() {
            Ok(value) => Ok(place.write_pin(value, slot)),
            Err(e) => Err(InitPinError { error: e, place, slot }),
        }
    }
}

impl<T, F, E> Init for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        match (self.0)() {
            Ok(value) => Ok(place.write(value)),
            Err(e) => Err(InitError { error: e, place }),
        }
    }
}

pub const fn try_with<T, F, E>(f: F) -> TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    TryWith(f)
}

impl<T, E, F> IntoInit<T, TryWith<F>> for F
where
    F: FnOnce() -> Result<T, E>,
{
    type Init = TryWith<F>;
    type Error = E;

    fn into_init(self) -> Self::Init {
        TryWith(self)
    }
}

pub struct With<F>(F);

impl<T, F> InitPin for With<F>
where
    F: FnOnce() -> T,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        place.try_write_pin::<_, Value<T>>((self.0)(), slot)
    }
}

impl<T, F> Init for With<F>
where
    F: FnOnce() -> T,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        place.try_write((self.0)())
    }
}

pub const fn with<T, F>(f: F) -> With<F>
where
    F: FnOnce() -> T,
{
    With(f)
}

impl<T, F> IntoInit<T, With<F>> for F
where
    F: FnOnce() -> T,
{
    type Init = With<F>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        With(self)
    }
}
