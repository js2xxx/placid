use core::{
    cell::{Cell, UnsafeCell},
    marker::PhantomPinned,
    mem::{self, ManuallyDrop},
};

use crate::{init::*, pin::DropSlot, uninit::Uninit};

#[doc(hidden)]
pub struct InitCell<'a, T: ?Sized, const C: bool> {
    uninit: Uninit<'a, Cell<T>>,
}

impl<'a, T: ?Sized, const C: bool> InitCell<'a, T, C> {
    #[doc(hidden)]
    #[inline]
    unsafe fn __drop_init(&mut self) {
        let base = self.uninit.as_mut_ptr();
        if C {
            unsafe { base.drop_in_place() };
        }
    }
    #[doc(hidden)]
    #[inline]
    fn __err<E>(self, err: E) -> InitError<'a, Cell<T>, E> {
        let mut this = mem::ManuallyDrop::new(self);
        unsafe { this.__drop_init() };
        InitError {
            error: err,
            place: unsafe { core::ptr::read(&this.uninit) },
        }
    }
}

impl<'a, T: ?Sized, const C: bool> Drop for InitCell<'a, T, C> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.__drop_init() };
    }
}

impl<'a, T: ?Sized> InitCell<'a, T, false> {
    #[inline]
    pub fn __next<A, E, M>(
        mut self,
        init: A,
    ) -> Result<InitCell<'a, T, true>, InitError<'a, Cell<T>, E>>
    where
        A: IntoInit<T, M, Init: Init<T>, Error = E>,
    {
        let init = init.into_init();
        let field_place = unsafe { Uninit::from_raw(self.uninit.as_mut_ptr() as *mut T) };
        match init.init(field_place) {
            Ok(own) => {
                mem::forget(own);
                Ok(
                    unsafe {
                        mem::transmute::<InitCell<'a, T, false>, InitCell<'a, T, true>>(self)
                    },
                )
            }
            Err(err) => Err(self.__err(err.error)),
        }
    }
}

impl<'a, T: ?Sized> InitCell<'a, T, true> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> Own<'a, Cell<T>> {
        let this = mem::ManuallyDrop::new(self);
        unsafe {
            let uninit = core::ptr::read(&this.uninit);
            uninit.assume_init()
        }
    }
}

impl<'a, T: ?Sized + 'a> StructuralInit<'a> for Cell<T> {
    type __BuilderInit = InitCell<'a, T, false>;
    #[inline]
    fn __builder_init(uninit: Uninit<'a, Cell<T>>) -> InitCell<'a, T, false> {
        InitCell { uninit }
    }
}

#[doc(hidden)]
pub struct InitPinCell<'a, 'b, T: ?Sized, const C: bool> {
    uninit: Uninit<'a, Cell<T>>,
    slot: DropSlot<'a, 'b, Cell<T>>,
}

impl<'a, 'b, T: ?Sized, const C: bool> InitPinCell<'a, 'b, T, C> {
    #[doc(hidden)]
    #[inline]
    unsafe fn __drop_init(&mut self) {
        let base = self.uninit.as_mut_ptr();
        if C {
            unsafe { base.drop_in_place() };
        }
    }
    #[doc(hidden)]
    #[inline]
    fn __err<E>(self, err: E) -> InitPinError<'a, 'b, Cell<T>, E> {
        let mut this = mem::ManuallyDrop::new(self);
        unsafe { this.__drop_init() };
        InitPinError {
            error: err,
            place: unsafe { core::ptr::read(&this.uninit) },
            slot: unsafe { core::ptr::read(&this.slot) },
        }
    }
}

impl<'a, 'b, T: ?Sized, const C: bool> Drop for InitPinCell<'a, 'b, T, C> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.__drop_init() };
    }
}

impl<'a, 'b, T: ?Sized> InitPinCell<'a, 'b, T, false> {
    #[inline]
    pub fn __next<A, E, M>(
        mut self,
        init: A,
    ) -> Result<InitPinCell<'a, 'b, T, true>, InitPinError<'a, 'b, Cell<T>, E>>
    where
        A: IntoInit<T, M, Error = E>,
    {
        let init = init.into_init();
        let mut slot = mem::ManuallyDrop::new(crate::pin::DroppingSlot::new());
        let slot_ref = unsafe {
            mem::transmute::<DropSlot<'_, '_, T>, DropSlot<'a, 'b, T>>(DropSlot::new_unchecked(
                &mut slot,
            ))
        };
        let field_place = unsafe { Uninit::from_raw(self.uninit.as_mut_ptr() as *mut T) };
        match init.init_pin(field_place, slot_ref) {
            Ok(own) => {
                mem::forget(own);
                Ok(unsafe {
                    let this = ManuallyDrop::new(self);
                    let uninit = core::ptr::read(&this.uninit);
                    let slot = core::ptr::read(&this.slot);
                    InitPinCell { uninit, slot }
                })
            }
            Err(err) => Err(self.__err(err.error)),
        }
    }
}

impl<'a, 'b, T: ?Sized> InitPinCell<'a, 'b, T, true> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> POwn<'b, Cell<T>> {
        let this = mem::ManuallyDrop::new(self);
        unsafe {
            let uninit = core::ptr::read(&this.uninit);
            let slot = core::ptr::read(&this.slot);
            uninit.assume_init_pin(slot)
        }
    }
}

impl<'b, T: 'b + ?Sized> StructuralInitPin<'b> for Cell<T> {
    type __BuilderInitPin<'a: 'b>
        = InitPinCell<'a, 'b, T, false>
    where
        Self: 'a;

    #[inline]
    fn __builder_init_pin<'a>(
        uninit: Uninit<'a, Cell<T>>,
        slot: DropSlot<'a, 'b, Cell<T>>,
    ) -> InitPinCell<'a, 'b, T, false>
    where
        Self: 'a,
    {
        InitPinCell { uninit, slot }
    }
}

#[doc(hidden)]
pub struct InitUnsafeCell<'a, T: ?Sized, const C: bool> {
    uninit: Uninit<'a, UnsafeCell<T>>,
}

impl<'a, T: ?Sized, const C: bool> InitUnsafeCell<'a, T, C> {
    #[doc(hidden)]
    #[inline]
    unsafe fn __drop_init(&mut self) {
        let base = self.uninit.as_mut_ptr();
        if C {
            unsafe { base.drop_in_place() };
        }
    }
    #[doc(hidden)]
    #[inline]
    fn __err<E>(self, err: E) -> InitError<'a, UnsafeCell<T>, E> {
        let mut this = mem::ManuallyDrop::new(self);
        unsafe { this.__drop_init() };
        InitError {
            error: err,
            place: unsafe { core::ptr::read(&this.uninit) },
        }
    }
}

impl<'a, T: ?Sized, const C: bool> Drop for InitUnsafeCell<'a, T, C> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.__drop_init() };
    }
}

impl<'a, T: ?Sized> InitUnsafeCell<'a, T, false> {
    #[inline]
    pub fn __next<A, E, M>(
        mut self,
        init: A,
    ) -> Result<InitUnsafeCell<'a, T, true>, InitError<'a, UnsafeCell<T>, E>>
    where
        A: IntoInit<T, M, Init: Init<T>, Error = E>,
    {
        let init = init.into_init();
        let field_place = unsafe { Uninit::from_raw(self.uninit.as_mut_ptr() as *mut T) };
        match init.init(field_place) {
            Ok(own) => {
                mem::forget(own);
                Ok(unsafe {
                    mem::transmute::<InitUnsafeCell<'a, T, false>, InitUnsafeCell<'a, T, true>>(
                        self,
                    )
                })
            }
            Err(err) => Err(self.__err(err.error)),
        }
    }
}

impl<'a, T: ?Sized> InitUnsafeCell<'a, T, true> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> Own<'a, UnsafeCell<T>> {
        let this = mem::ManuallyDrop::new(self);
        unsafe {
            let uninit = core::ptr::read(&this.uninit);
            uninit.assume_init()
        }
    }
}

impl<'a, T: Sized + 'a> StructuralInit<'a> for UnsafeCell<T> {
    type __BuilderInit = InitUnsafeCell<'a, T, false>;
    #[inline]
    fn __builder_init(uninit: Uninit<'a, UnsafeCell<T>>) -> InitUnsafeCell<'a, T, false> {
        InitUnsafeCell { uninit }
    }
}

#[doc(hidden)]
pub struct InitPinUnsafeCell<'a, 'b, T: ?Sized, const C: bool> {
    uninit: Uninit<'a, UnsafeCell<T>>,
    slot: DropSlot<'a, 'b, UnsafeCell<T>>,
}

impl<'a, 'b, T: ?Sized, const C: bool> InitPinUnsafeCell<'a, 'b, T, C> {
    #[doc(hidden)]
    #[inline]
    unsafe fn __drop_init(&mut self) {
        let base = self.uninit.as_mut_ptr();
        if C {
            unsafe { base.drop_in_place() };
        }
    }
    #[doc(hidden)]
    #[inline]
    fn __err<E>(self, err: E) -> InitPinError<'a, 'b, UnsafeCell<T>, E> {
        let mut this = mem::ManuallyDrop::new(self);
        unsafe { this.__drop_init() };
        InitPinError {
            error: err,
            place: unsafe { core::ptr::read(&this.uninit) },
            slot: unsafe { core::ptr::read(&this.slot) },
        }
    }
}

impl<'a, 'b, T: ?Sized, const C: bool> Drop for InitPinUnsafeCell<'a, 'b, T, C> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.__drop_init() };
    }
}

impl<'a, 'b, T: ?Sized> InitPinUnsafeCell<'a, 'b, T, false> {
    #[inline]
    pub fn __next<A, E, M>(
        mut self,
        init: A,
    ) -> Result<InitPinUnsafeCell<'a, 'b, T, true>, InitPinError<'a, 'b, UnsafeCell<T>, E>>
    where
        A: IntoInit<T, M, Error = E>,
    {
        let init = init.into_init();
        let mut slot = mem::ManuallyDrop::new(crate::pin::DroppingSlot::new());
        let slot_ref = unsafe {
            mem::transmute::<DropSlot<'_, '_, T>, DropSlot<'a, 'b, T>>(DropSlot::new_unchecked(
                &mut slot,
            ))
        };
        let field_place = unsafe { Uninit::from_raw(self.uninit.as_mut_ptr() as *mut T) };
        match init.init_pin(field_place, slot_ref) {
            Ok(own) => {
                mem::forget(own);
                Ok(unsafe {
                    let this = ManuallyDrop::new(self);
                    let uninit = core::ptr::read(&this.uninit);
                    let slot = core::ptr::read(&this.slot);
                    InitPinUnsafeCell { uninit, slot }
                })
            }
            Err(err) => Err(self.__err(err.error)),
        }
    }
}

impl<'a, 'b, T: ?Sized> InitPinUnsafeCell<'a, 'b, T, true> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> POwn<'b, UnsafeCell<T>> {
        let this = mem::ManuallyDrop::new(self);
        unsafe {
            let uninit = core::ptr::read(&this.uninit);
            let slot = core::ptr::read(&this.slot);
            uninit.assume_init_pin(slot)
        }
    }
}

impl<'b, T: 'b + ?Sized> StructuralInitPin<'b> for UnsafeCell<T> {
    type __BuilderInitPin<'a: 'b>
        = InitPinUnsafeCell<'a, 'b, T, false>
    where
        Self: 'a;

    #[inline]
    fn __builder_init_pin<'a>(
        uninit: Uninit<'a, UnsafeCell<T>>,
        slot: DropSlot<'a, 'b, UnsafeCell<T>>,
    ) -> InitPinUnsafeCell<'a, 'b, T, false>
    where
        Self: 'a,
    {
        InitPinUnsafeCell { uninit, slot }
    }
}

#[doc(hidden)]
pub struct InitPhantomPinned<'a> {
    uninit: Uninit<'a, PhantomPinned>,
}

impl<'a> InitPhantomPinned<'a> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> Own<'a, PhantomPinned> {
        unsafe { self.uninit.assume_init() }
    }
}

impl<'a> StructuralInit<'a> for PhantomPinned {
    type __BuilderInit = InitPhantomPinned<'a>;
    #[inline]
    fn __builder_init(uninit: Uninit<'a, PhantomPinned>) -> InitPhantomPinned<'a> {
        InitPhantomPinned { uninit }
    }
}

#[doc(hidden)]
pub struct InitPinPhantomPinned<'a, 'b> {
    uninit: Uninit<'a, PhantomPinned>,
    slot: DropSlot<'a, 'b, PhantomPinned>,
}

impl<'a, 'b> InitPinPhantomPinned<'a, 'b> {
    #[inline]
    #[doc(hidden)]
    pub fn build(self) -> POwn<'b, PhantomPinned> {
        unsafe { self.uninit.assume_init_pin(self.slot) }
    }
}

impl<'b> StructuralInitPin<'b> for PhantomPinned {
    type __BuilderInitPin<'a: 'b>
        = InitPinPhantomPinned<'a, 'b>
    where
        Self: 'a;

    #[inline]
    fn __builder_init_pin<'a>(
        uninit: Uninit<'a, PhantomPinned>,
        slot: DropSlot<'a, 'b, PhantomPinned>,
    ) -> InitPinPhantomPinned<'a, 'b>
    where
        Self: 'a,
    {
        InitPinPhantomPinned { uninit, slot }
    }
}
