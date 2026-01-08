use core::pin::Pin;

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinError},
    pin::{DropSlot, POwn},
};

pub struct And<I, F> {
    init: I,
    f: F,
}

impl<I: Init, F: FnOnce(&mut I::Target)> InitPin for And<I, F> {
    type Target = I::Target;
    type Error = I::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, Self::Target>,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> Result<POwn<'b, Self::Target>, InitPinError<'a, 'b, Self::Target, Self::Error>> {
        let mut own = match self.init.init(place) {
            Ok(own) => own,
            Err(err) => return Err(err.into_pin(slot)),
        };
        (self.f)(&mut *own);
        Ok(Own::into_pin(own, slot))
    }
}

impl<I: Init, F: FnOnce(&mut I::Target)> Init for And<I, F> {
    fn init(
        self,
        place: Uninit<'_, I::Target>,
    ) -> Result<Own<'_, I::Target>, InitError<'_, I::Target, Self::Error>> {
        let mut own = self.init.init(place)?;
        (self.f)(&mut *own);
        Ok(own)
    }
}

pub fn and<I, F>(init: I, f: F) -> And<I, F>
where
    I: Init,
    F: FnOnce(&mut I::Target),
{
    And { init, f }
}

pub struct AndPin<I, F> {
    init: I,
    f: F,
}

impl<I: InitPin, F: FnOnce(Pin<&mut I::Target>)> InitPin for AndPin<I, F> {
    type Target = I::Target;
    type Error = I::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, Self::Target>,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> Result<POwn<'b, Self::Target>, InitPinError<'a, 'b, Self::Target, Self::Error>> {
        let mut own = self.init.init_pin(place, slot)?;
        (self.f)(own.as_mut());
        Ok(own)
    }
}

pub fn and_pin<I, F>(init: I, f: F) -> AndPin<I, F>
where
    I: InitPin,
    F: FnOnce(Pin<&mut I::Target>),
{
    AndPin { init, f }
}
