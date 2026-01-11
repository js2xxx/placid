use core::pin::Pin;

use crate::{
    init::{Init, InitPin, InitPinResult, InitResult, Initializer, IntoInit, IntoInitPin},
    owned::Own,
    pin::DropSlot,
    uninit::Uninit,
};

/// Chains initialization with a post-initialization closure for mutable access.
///
/// This initializer is created by calling the [`Init::and`] method, or by using
/// the [`and()`] factory function. It's chainable with other initializers.
///
/// [`Init`]: crate::init::Init
#[derive(Debug, PartialEq)]
pub struct And<I, F> {
    init: I,
    f: F,
}

impl<I, F> Initializer for And<I, F>
where
    I: Initializer,
{
    type Error = I::Error;
}

impl<T, I, F> InitPin<T> for And<I, F>
where
    T: ?Sized,
    I: Init<T>,
    F: FnOnce(&mut T),
{
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, I::Error> {
        let mut own = match self.init.init(place) {
            Ok(own) => own,
            Err(e) => return Err(e.into_pin(slot)),
        };
        (self.f)(&mut *own);
        Ok(Own::into_pin(own, slot))
    }
}

impl<T, I, F> Init<T> for And<I, F>
where
    T: ?Sized,
    I: Init<T>,
    F: FnOnce(&mut T),
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, I::Error> {
        let mut own = self.init.init(place)?;
        (self.f)(&mut *own);
        Ok(own)
    }
}

/// Chains initialization with a post-initialization closure for mutable access.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let owned: Own<Vec<_>> = own!(init::and(vec![1, 2, 3], |v| v.push(4)));
/// assert_eq!(*owned, vec![1, 2, 3, 4]);
/// ```
pub fn and<M, I, F, T: ?Sized>(init: I, f: F) -> And<I::Init, F>
where
    I: IntoInit<T, M>,
    F: FnOnce(&mut T),
{
    And { init: init.into_init(), f }
}

/// Chains initialization with a post-initialization closure for pinned mutable
/// access.
///
/// This initializer is created by calling the [`InitPin::and_pin`] method, or
/// by using the [`and_pin()`] factory function. It's chainable with other
/// initializers.
#[derive(Debug, PartialEq)]
pub struct AndPin<I, F> {
    init: I,
    f: F,
}

impl<I, F> Initializer for AndPin<I, F>
where
    I: Initializer,
{
    type Error = I::Error;
}

impl<T, I, F> InitPin<T> for AndPin<I, F>
where
    T: ?Sized,
    I: InitPin<T>,
    F: FnOnce(Pin<&mut T>),
{
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, I::Error> {
        let mut own = self.init.init_pin(place, slot)?;
        (self.f)(own.as_mut());
        Ok(own)
    }
}

/// Chains initialization with a post-initialization closure for pinned mutable
/// access.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
/// use core::pin::Pin;
///
/// let owned = pown!(init::and_pin(
///     vec![1, 2, 3],
///     |mut v| v.as_mut().push(4),
/// ));
/// assert_eq!(*owned, [1, 2, 3, 4]);
/// ```
pub fn and_pin<M, I, F, T: ?Sized>(init: I, f: F) -> AndPin<I::Init, F>
where
    I: IntoInitPin<T, M>,
    F: FnOnce(Pin<&mut T>),
{
    AndPin { init: init.into_init(), f }
}
