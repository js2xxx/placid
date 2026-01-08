use core::pin::Pin;

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinError, IntoInit},
    pin::{DropSlot, POwn},
};

/// Chains initialization with a post-initialization closure for mutable access.
///
/// This initializer is created by calling the [`Init::and`] method, or by using
/// the [`and()`] factory function. It's chainable with other initializers.
///
/// [`Init`]: crate::init::Init
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

/// Chains initialization with a post-initialization closure for mutable access.
///
/// # Examples
///
/// ```rust
/// use placid::{place, Own, init::*};
///
/// let owned: Own<Vec<_>> = place!(and(vec![1, 2, 3], |v| v.push(4)));
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

/// Chains initialization with a post-initialization closure for pinned mutable
/// access.
///
/// # Examples
///
/// ```rust
/// use placid::{place, POwn, init::*};
/// use core::pin::Pin;
///
/// let owned: POwn<Vec<_>> = place!(@pin and_pin(
///     vec![1, 2, 3],
///     |mut v: Pin<&mut Vec<_>>| v.as_mut().push(4),
/// ));
/// assert_eq!(*owned, [1, 2, 3, 4]);
/// ```
pub fn and_pin<M, I, F, T: ?Sized>(init: I, f: F) -> AndPin<I::Init, F>
where
    I: IntoInit<T, M>,
    F: FnOnce(Pin<&mut T>),
{
    AndPin { init: init.into_init(), f }
}
