use core::{convert::Infallible, marker::PhantomData};

use crate::{init::*, pin::DropSlot, uninit::Uninit};

/// Provides a fallback initializer if the primary one fails.
///
/// This initializer is created by calling the [`InitPin::or`] method or by
/// using the [`or()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Or<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<I1, I2, M> Initializer for Or<I1, I2, M>
where
    I1: Initializer,
{
    type Error = I1::Error;
}

impl<T: ?Sized, I1, M, I2> InitPin<T> for Or<I1, I2, M>
where
    I1: InitPin<T>,
    I2: IntoInitPin<T, M, Error: Into<I1::Error>>,
{
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
    I2: IntoInit<T, M, Error: Into<I1::Error>>,
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
/// use placid::prelude::*;
///
/// let owned: Own<u32> = own!(init::or(
///     init::value(10u32),
///     init::value(20u32),
/// ));
/// assert_eq!(*owned, 10);
///
/// let failed: Own<u32> = own!(init::or(
///     init::try_with(|| u32::try_from(-1i32)),
///     init::value(30u32),
/// ));
/// assert_eq!(*failed, 30);
/// ```
pub fn or<T: ?Sized, I1, I2, M2>(init1: I1, init2: I2) -> Or<I1, I2, M2>
where
    I1: InitPin<T>,
    I2: IntoInitPin<T, M2, Error: Into<I1::Error>>,
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
#[derive(Debug, PartialEq)]
pub struct OrElse<I, F> {
    init1: I,
    f: F,
}

impl<I, F, I2> Initializer for OrElse<I, F>
where
    I: Initializer,
    F: FnOnce(I::Error) -> I2,
    I2: Initializer<Error: Into<I::Error>>,
{
    type Error = I::Error;
}

impl<T: ?Sized, I1: InitPin<T>, F, I2> InitPin<T> for OrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error: Into<I1::Error>>,
{
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
/// use placid::prelude::*;
///
/// let owned: Own<u32> = own!(init::or_else(
///     init::try_with(|| u32::try_from(-1i32)),
///     |err| {
///         println!("Initialization failed with error: {}", err);
///         init::value(42u32)
///     },
/// ));
/// assert_eq!(*owned, 42);
/// ```
pub const fn or_else<I1, F, I2>(init1: I1, f: F) -> OrElse<I1, F>
where
    I1: Initializer,
    F: FnOnce(I1::Error) -> I2,
    I2: Initializer<Error: Into<I1::Error>>,
{
    OrElse { init1, f }
}

/// Provides a fallback initializer if the primary one fails. The fallback
/// initializer must be infallible.
///
/// This initializer is created by calling the [`InitPin::unwrap_or`] method or
/// by using the [`unwrap_or()`] factory function.
#[derive(Debug, PartialEq)]
pub struct UnwrapOr<I1, I2, M> {
    init1: I1,
    init2: I2,
    marker: PhantomData<M>,
}

impl<I1, I2, M> Initializer for UnwrapOr<I1, I2, M>
where
    I1: Initializer,
{
    type Error = Infallible;
}

impl<T: ?Sized, I1, M, I2> InitPin<T> for UnwrapOr<I1, I2, M>
where
    I1: InitPin<T>,
    I2: IntoInitPin<T, M, Error = Infallible>,
{
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
    I2: IntoInit<T, M, Error = Infallible>,
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
/// use placid::prelude::*;
///
/// let owned: Own<u32> = own!(init::unwrap_or(
///     init::value(10u32),
///     init::value(20u32),
/// ));
/// assert_eq!(*owned, 10);
///
/// let failed: Own<u32> = own!(init::unwrap_or(
///     init::try_with(|| u32::try_from(-1i32)),
///     init::value(30u32),
/// ));
/// assert_eq!(*failed, 30);
/// ```
pub const fn unwrap_or<T: ?Sized, I1, I2, M2>(init1: I1, init2: I2) -> UnwrapOr<I1, I2, M2>
where
    I1: Initializer,
    I2: IntoInitPin<T, M2, Error = Infallible>,
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
#[derive(Debug, PartialEq)]
pub struct UnwrapOrElse<I, F> {
    init1: I,
    f: F,
}

impl<I1, F, I2> Initializer for UnwrapOrElse<I1, F>
where
    I1: Initializer,
    F: FnOnce(I1::Error) -> I2,
    I2: Initializer<Error = Infallible>,
{
    type Error = Infallible;
}

impl<T: ?Sized, I1: InitPin<T>, F, I2> InitPin<T> for UnwrapOrElse<I1, F>
where
    F: FnOnce(I1::Error) -> I2,
    I2: InitPin<T, Error = Infallible>,
{
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
/// use placid::prelude::*;
///
/// let owned: Own<u32> = own!(init::unwrap_or_else(
///     init::try_with(|| u32::try_from(-1i32)),
///     |err| {
///         println!("Initialization failed with error: {}", err);
///         init::value(42u32)
///     },
/// ));
/// assert_eq!(*owned, 42);
/// ```
pub const fn unwrap_or_else<I1, F, I2>(init1: I1, f: F) -> UnwrapOrElse<I1, F>
where
    I1: Initializer,
    F: FnOnce(I1::Error) -> I2,
    I2: Initializer<Error = Infallible>,
{
    UnwrapOrElse { init1, f }
}

/// Maps the error type of an initializer using a closure.
///
/// This initializer is created by calling the [`Initializer::map_err`] methods,
/// or by using the [`map_err()`] factory function.
#[derive(Debug, PartialEq)]
pub struct MapErr<I, F> {
    init: I,
    f: F,
}

impl<I, F, E: core::fmt::Debug> Initializer for MapErr<I, F>
where
    I: Initializer,
    F: FnOnce(I::Error) -> E,
{
    type Error = E;
}

impl<T, I, F, E: core::fmt::Debug> InitPin<T> for MapErr<I, F>
where
    T: ?Sized,
    I: InitPin<T>,
    F: FnOnce(I::Error) -> E,
{
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, E> {
        self.init.init_pin(place, slot).map_err(|e| e.map(self.f))
    }
}

impl<T, I, F, E: core::fmt::Debug> Init<T> for MapErr<I, F>
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
/// use placid::prelude::*;
///
/// let mut uninit = uninit!(i32);
/// let res = uninit.try_write(
///     init::try_with(|| -> Result<_, &str> { Err("initialization failed") })
///         .map_err(|e| format!("Error occurred: {}", e))
/// );
/// assert!(res.is_err());
/// assert_eq!(
///     res.err().unwrap().error,
///     "Error occurred: initialization failed"
/// );
/// ```
pub const fn map_err<I, F, E>(init: I, f: F) -> MapErr<I, F>
where
    I: Initializer,
    F: FnOnce(I::Error) -> E,
{
    MapErr { init, f }
}

/// Adapts an infallible initializer to one that can fail with any error type.
///
/// Since the original initializer cannot fail, the provided closure will never
/// be called.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
/// use std::num::TryFromIntError;
///
/// let owned: Own<u32> = own!(init::adapt_err::<_, TryFromIntError>(
///     init::value(100u32),
/// ));
/// assert_eq!(*owned, 100);
/// ```
pub const fn adapt_err<I, E>(init: I) -> MapErr<I, impl FnOnce(Infallible) -> E>
where
    I: Initializer<Error = Infallible>,
{
    map_err(init, |e| match e {})
}
