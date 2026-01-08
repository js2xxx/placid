use core::marker::PhantomData;

use crate::{
    Init, InitPin, Own, Uninit,
    init::{InitError, InitPinResult, IntoInit},
    pin::DropSlot,
};

/// Provides a fallback initializer if the primary one fails.
///
/// This initializer is created by calling the [`InitPin::or`] method or by
/// using the [`or()`] factory function.
pub struct Or<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<I1: InitPin, M, I2: IntoInit<I1::Target, M, Error: Into<I1::Error>>> InitPin
    for Or<I1, I2, M>
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
            Err(err) => (self.init2.into_init())
                .init_pin(err.place, err.slot)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

impl<I1: Init, M, I2: IntoInit<I1::Target, M, Init: Init, Error: Into<I1::Error>>> Init
    for Or<I1, I2, M>
{
    fn init(
        self,
        place: Uninit<'_, Self::Target>,
    ) -> Result<Own<'_, Self::Target>, InitError<'_, Self::Target, Self::Error>> {
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
/// use placid::{place, Own, init::*};
///
/// let owned: Own<u32> = place!(or(value(10u32), value(20u32)));
/// assert_eq!(*owned, 10);
///
/// let failed: Own<u32> = place!(or(try_with(|| u32::try_from(-1i32)), 30u32));
/// assert_eq!(*failed, 30);
/// ```
pub fn or<I1, I2, M2>(init1: I1, init2: I2) -> Or<I1, I2, M2>
where
    I1: InitPin,
    I2: IntoInit<I1::Target, M2, Error: Into<I1::Error>>,
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
pub struct OrElse<I, F> {
    init1: I,
    f: F,
}

impl<I1: InitPin, F, I2> InitPin for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<Target = I1::Target, Error: Into<I1::Error>>,
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
            Err(err) => (self.f)(err.error)
                .init_pin(err.place, err.slot)
                .map_err(|e| e.map(Into::into)),
        }
    }
}

impl<I1: Init, F, I2> Init for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: Init<Target = I1::Target, Error: Into<I1::Error>>,
{
    fn init(
        self,
        place: Uninit<'_, Self::Target>,
    ) -> Result<Own<'_, Self::Target>, InitError<'_, Self::Target, Self::Error>> {
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
/// use placid::{place, Own, init::*};
///
/// let owned: Own<u32> = place!(or_else(try_with(|| u32::try_from(-1i32)), |err| {
///     println!("Initialization failed with error: {}", err);
///     value(42u32)
/// }));
/// assert_eq!(*owned, 42);
/// ```
pub const fn or_else<I1, F, I2>(init1: I1, f: F) -> OrElse<I1, F>
where
    I1: InitPin,
    F: FnOnce(I1::Error) -> I2,
{
    OrElse { init1, f }
}
