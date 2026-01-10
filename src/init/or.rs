use core::marker::PhantomData;

use crate::{
    Init, InitPin, Uninit,
    init::{InitPinResult, InitResult, IntoInit},
    pin::DropSlot,
};

/// Provides a fallback initializer if the primary one fails.
///
/// This initializer is created by calling the [`InitPin::or`] method or by
/// using the [`or()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Or<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<T: ?Sized, I1, M, I2> InitPin<T> for Or<I1, I2, M>
where
    I1: InitPin<T>,
    I2: IntoInit<T, M, Error: Into<I1::Error>>,
{
    type Error = I1::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, I1::Error> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => (self.init2.into_init())
                .init_pin(err.place, err.slot)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

impl<T: ?Sized, I1, M, I2> Init<T> for Or<I1, I2, M>
where
    I1: Init<T>,
    I2: IntoInit<T, M, Init: Init<T>, Error: Into<I1::Error>>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, I1::Error> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => (self.init2.into_init())
                .init(err.place)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

/// Provides a fallback initializer if the primary one fails.
///
/// # Examples
///
/// ```rust
/// use placid::{own, Own, init::*};
///
/// let owned: Own<u32> = own!(or(value(10u32), value(20u32)));
/// assert_eq!(*owned, 10);
///
/// let failed: Own<u32> = own!(or(try_with(|| u32::try_from(-1i32)), 30u32));
/// assert_eq!(*failed, 30);
/// ```
pub fn or<T: ?Sized, I1, I2, M2>(init1: I1, init2: I2) -> Or<I1, I2, M2>
where
    I1: InitPin<T>,
    I2: IntoInit<T, M2, Error: Into<I1::Error>>,
{
    Or {
        init1,
        init2,
        marker: PhantomData,
    }
}

/// Provides a fallback initializer computed from the error of the primary one.
///
/// This initializer is created by calling the [`InitPin::or_else`] method or by
/// using the [`or_else()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OrElse<I, F> {
    init1: I,
    f: F,
}

impl<T: ?Sized, I1: InitPin<T>, F, I2> InitPin<T> for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error: Into<I1::Error>>,
{
    type Error = I1::Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, I1::Error> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => (self.f)(err.error)
                .init_pin(err.place, err.slot)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

impl<T: ?Sized, I1: Init<T>, F, I2> Init<T> for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: Init<T, Error: Into<I1::Error>>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, I1::Error> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => (self.f)(err.error)
                .init(err.place)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

/// Provides a fallback initializer computed from the error of the primary one.
///
/// # Examples
///
/// ```rust
/// use placid::{own, Own, init::*};
///
/// let owned: Own<u32> = own!(or_else(try_with(|| u32::try_from(-1i32)), |err| {
///     println!("Initialization failed with error: {}", err);
///     value(42u32)
/// }));
/// assert_eq!(*owned, 42);
/// ```
pub const fn or_else<T: ?Sized, I1, F, I2>(init1: I1, f: F) -> OrElse<I1, F>
where
    I1: InitPin<T>,
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error: Into<I1::Error>>,
{
    OrElse { init1, f }
}
