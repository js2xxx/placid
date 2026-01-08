use core::pin::Pin;

use crate::{
    Own, Uninit,
    init::{Error, Init, InitPin},
    pin::{DropSlot, POwn},
};

pub enum AndInspect {}

pub struct Inspect<I, F> {
    init: I,
    f: F,
}

impl<T: ?Sized, M, I: Init<T, M>, F: FnOnce(&mut T)> InitPin<T, (AndInspect, M)> for Inspect<I, F> {
    type Error = I::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        let mut own = self.init.init(place)?;
        (self.f)(&mut *own);
        Ok(Own::into_pin(own, slot))
    }
}

impl<T: ?Sized, M, I: Init<T, M>, F: FnOnce(&mut T)> Init<T, (AndInspect, M)> for Inspect<I, F> {
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        let mut own = self.init.init(place)?;
        (self.f)(&mut *own);
        Ok(own)
    }
}

pub fn inspect<T, M, I, F>(init: I, f: F) -> Inspect<I, F>
where
    T: ?Sized,
    I: Init<T, M>,
    F: FnOnce(&mut T),
{
    Inspect { init, f }
}

pub enum AndInspectPin {}

impl<T: ?Sized, M, I: InitPin<T, M>, F: FnOnce(Pin<&mut T>)> InitPin<T, (AndInspectPin, M)>
    for Inspect<I, F>
{
    type Error = I::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        let mut own = self.init.init_pin(place, slot)?;
        (self.f)(own.as_mut());
        Ok(own)
    }
}

pub fn inspect_pin<T, M, I, F>(init: I, f: F) -> Inspect<I, F>
where
    T: ?Sized,
    I: InitPin<T, M>,
    F: FnOnce(Pin<&mut T>),
{
    Inspect { init, f }
}
