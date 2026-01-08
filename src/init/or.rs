use core::marker::PhantomData;

use crate::{
    Init, InitPin, Own, Uninit,
    init::{InitError, InitPinResult, IntoInit},
    pin::DropSlot,
};

pub struct Or<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<I1: InitPin, M, I2: IntoInit<I1::Target, M, Error = I1::Error>> InitPin for Or<I1, I2, M> {
    type Target = I1::Target;
    type Error = I1::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, Self::Target>,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> InitPinResult<'a, 'b, Self> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => self.init2.into_init().init_pin(err.place, err.slot),
        }
    }
}

impl<I1: Init, M, I2: IntoInit<I1::Target, M, Init: Init, Error = I1::Error>> Init
    for Or<I1, I2, M>
{
    fn init(
        self,
        place: Uninit<'_, Self::Target>,
    ) -> Result<Own<'_, Self::Target>, InitError<'_, Self::Target, Self::Error>> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => self.init2.into_init().init(err.place),
        }
    }
}

pub const fn or<I1, I2, M>(init1: I1, init2: I2) -> Or<I1, I2, M>
where
    I1: InitPin,
    I2: IntoInit<I1::Target, M, Error = I1::Error>,
{
    Or {
        init1,
        init2,
        marker: PhantomData,
    }
}

pub struct OrElse<I, F> {
    init1: I,
    f: F,
}

impl<I1: InitPin, F, I2> InitPin for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<Target = I1::Target, Error = I1::Error>,
{
    type Target = I1::Target;
    type Error = I1::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, Self::Target>,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> InitPinResult<'a, 'b, Self> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => {
                let init2 = (self.f)(err.error);
                init2.init_pin(err.place, err.slot)
            }
        }
    }
}

impl<I1: Init, F, I2> Init for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: Init<Target = I1::Target, Error = I1::Error>,
{
    fn init(
        self,
        place: Uninit<'_, Self::Target>,
    ) -> Result<Own<'_, Self::Target>, InitError<'_, Self::Target, Self::Error>> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => {
                let init2 = (self.f)(err.error);
                init2.init(err.place)
            }
        }
    }
}

pub const fn or_else<I1, F, I2>(init1: I1, f: F) -> OrElse<I1, F>
where
    I1: InitPin,
    F: FnOnce(I1::Error) -> I2,
{
    OrElse { init1, f }
}
