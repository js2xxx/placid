use core::{convert::Infallible, marker::PhantomData};

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

/// Provides a fallback initializer if the primary one fails. The fallback
/// initializer must be infallible.
///
/// This initializer is created by calling the [`InitPin::unwrap_or`] method or
/// by using the [`unwrap_or()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UnwrapOr<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<T: ?Sized, I1, M, I2> InitPin<T> for UnwrapOr<I1, I2, M>
where
    I1: InitPin<T>,
    I2: IntoInit<T, M, Error = Infallible>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => self.init2.into_init().init_pin(err.place, err.slot),
        }
    }
}

impl<T: ?Sized, I1, M, I2> Init<T> for UnwrapOr<I1, I2, M>
where
    I1: Init<T>,
    I2: IntoInit<T, M, Init: Init<T>, Error = Infallible>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, Infallible> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => self.init2.into_init().init(err.place),
        }
    }
}

/// Provides a fallback initializer if the primary one fails. The fallback
/// initializer must be infallible.
///
/// # Examples
///
/// ```rust
/// use placid::{own, Own, init::*};
///
/// let owned: Own<u32> = own!(unwrap_or(value(10u32), value(20u32)));
/// assert_eq!(*owned, 10);
///
/// let failed: Own<u32> = own!(unwrap_or(try_with(|| u32::try_from(-1i32)), 30u32));
/// assert_eq!(*failed, 30);
/// ```
pub fn unwrap_or<T: ?Sized, I1, I2, M2>(init1: I1, init2: I2) -> UnwrapOr<I1, I2, M2>
where
    I1: InitPin<T>,
    I2: IntoInit<T, M2, Error = Infallible>,
{
    UnwrapOr {
        init1,
        init2,
        marker: PhantomData,
    }
}

/// Provides a fallback initializer computed from the error of the primary one.
/// The fallback initializer must be infallible.
///
/// This initializer is created by calling the [`InitPin::unwrap_or_else`]
/// method or by using the [`unwrap_or_else()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UnwrapOrElse<I, F> {
    init1: I,
    f: F,
}

impl<T: ?Sized, I1: InitPin<T>, F, I2> InitPin<T> for UnwrapOrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error = Infallible>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        match self.init1.init_pin(place, slot) {
            Ok(own) => Ok(own),
            Err(err) => (self.f)(err.error).init_pin(err.place, err.slot),
        }
    }
}

impl<T: ?Sized, I1: Init<T>, F, I2> Init<T> for UnwrapOrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: Init<T, Error = Infallible>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, Infallible> {
        match self.init1.init(place) {
            Ok(own) => Ok(own),
            Err(err) => (self.f)(err.error).init(err.place),
        }
    }
}

/// Provides a fallback initializer computed from the error of the primary one.
/// The fallback initializer must be infallible.
///
/// # Examples
///
/// ```rust
/// use placid::{own, Own, init::*};
///
/// let owned: Own<u32> = own!(unwrap_or_else(
///     try_with(|| u32::try_from(-1i32)),
///     |err| {
///         println!("Initialization failed with error: {}", err);
///         value(42u32)
///     }
/// ));
/// assert_eq!(*owned, 42);
/// ```
pub const fn unwrap_or_else<T: ?Sized, I1, F, I2>(init1: I1, f: F) -> UnwrapOrElse<I1, F>
where
    I1: InitPin<T>,
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error = Infallible>,
{
    UnwrapOrElse { init1, f }
}

/// Maps the error type of an initializer using a closure.
///
/// This initializer is created by calling the [`Init::map_err`] or
/// [`InitPin::map_err`] methods, or by using the [`map_err()`] factory
/// function.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MapErr<I, F> {
    init: I,
    f: F,
}

impl<T, I, F, E> InitPin<T> for MapErr<I, F>
where
    T: ?Sized,
    I: InitPin<T>,
    F: FnOnce(I::Error) -> E,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, E> {
        self.init.init_pin(place, slot).map_err(|e| e.map(self.f))
    }
}

impl<T, I, F, E> Init<T> for MapErr<I, F>
where
    T: ?Sized,
    I: Init<T>,
    F: FnOnce(I::Error) -> E,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, E> {
        self.init.init(place).map_err(|e| e.map(self.f))
    }
}

/// Maps the error type of an initializer using a closure.
///
/// # Examples
///
/// ```rust
/// use placid::{uninit, init::*};
///
/// let mut uninit = uninit!(i32);
/// let res = uninit.try_write(
///     try_with(|| -> Result<_, &str> { Err("initialization failed") })
///         .map_err(|e| format!("Error occurred: {}", e))
/// );
/// assert!(res.is_err());
/// assert_eq!(
///     res.err().unwrap().error,
///     "Error occurred: initialization failed"
/// );
/// ```
pub fn map_err<M, I, F, T: ?Sized, E>(init: I, f: F) -> MapErr<I::Init, F>
where
    I: IntoInit<T, M>,
    F: FnOnce(I::Error) -> E,
{
    MapErr { init: init.into_init(), f }
}
