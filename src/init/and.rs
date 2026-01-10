use core::pin::Pin;

use crate::{
    Uninit,
    init::{Init, InitPin, InitPinResult, InitResult, IntoInit},
    pin::DropSlot,
};

/// Chains initialization with a post-initialization closure for mutable access.
///
/// This initializer is created by calling the [`Init::and`] method, or by using
/// the [`and()`] factory function. It's chainable with other initializers.
///
/// [`Init`]: crate::init::Init
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct And<I, F> {
    init: I,
    f: F,
}

impl<'b, T, I, F> InitPin<'b, T> for And<I, F>
where
    T: ?Sized + Unpin,
    I: Init<'b, T>,
    F: FnOnce(&mut T),
{
    type Error = I::Error;

    fn init_pin<'a>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, I::Error> {
        let mut own = self.init.init_pin(place, slot)?;
        (self.f)(&mut *own);
        Ok(own)
    }
}

impl<'b, T, I, F> Init<'b, T> for And<I, F>
where
    T: ?Sized + Unpin,
    I: Init<'b, T>,
    F: FnOnce(&mut T),
{
    fn init(self, place: Uninit<'b, T>) -> InitResult<'b, T, I::Error> {
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
/// use placid::{own, Own, init::*};
///
/// let owned: Own<Vec<_>> = own!(and(vec![1, 2, 3], |v| v.push(4)));
/// assert_eq!(*owned, vec![1, 2, 3, 4]);
/// ```
pub fn and<'b, M, I, F, T: ?Sized + Unpin>(init: I, f: F) -> And<I::Init, F>
where
    I: IntoInit<'b, T, M>,
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
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AndPin<I, F> {
    init: I,
    f: F,
}

impl<'b, T, I, F> InitPin<'b, T> for AndPin<I, F>
where
    T: ?Sized,
    I: InitPin<'b, T>,
    F: FnOnce(Pin<&mut T>),
{
    type Error = I::Error;

    fn init_pin<'a>(
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
/// use placid::{pown, POwn, init::*};
/// use core::pin::Pin;
///
/// let owned: POwn<Vec<_>> = pown!(and_pin(
///     vec![1, 2, 3],
///     |mut v| v.as_mut().push(4),
/// ));
/// assert_eq!(*owned, [1, 2, 3, 4]);
/// ```
pub fn and_pin<'b, M, I, F, T: ?Sized>(init: I, f: F) -> AndPin<I::Init, F>
where
    I: IntoInit<'b, T, M>,
    F: FnOnce(Pin<&mut T>),
{
    AndPin { init: init.into_init(), f }
}
