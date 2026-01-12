use core::{
    cell::{Cell, UnsafeCell},
    marker::PhantomPinned,
    mem::{self, ManuallyDrop},
};

use crate::{init::*, pin::DropSlot, uninit::Uninit};

macro_rules! derive_value_wrapper {
    ($($ty:ident: ($pin:ident, $unpin:ident)),* $(,)?) => {$(
        #[doc(hidden)]
        pub struct $unpin<'a, T: ?Sized, const C: bool> {
            uninit: Uninit<'a, $ty<T>>,
        }

        impl<'a, T: ?Sized, const C: bool> $unpin<'a, T, C> {
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
            fn __err<E>(self, err: E) -> InitError<'a, $ty<T>, E> {
                let mut this = mem::ManuallyDrop::new(self);
                unsafe { this.__drop_init() };
                InitError {
                    error: err,
                    place: unsafe { core::ptr::read(&this.uninit) },
                }
            }
        }

        impl<'a, T: ?Sized, const C: bool> Drop for $unpin<'a, T, C> {
            #[inline]
            fn drop(&mut self) {
                unsafe { self.__drop_init() };
            }
        }

        impl<'a, T: ?Sized> $unpin<'a, T, false> {
            #[inline]
            pub fn __next<A, E, M>(
                mut self,
                init: A,
            ) -> Result<$unpin<'a, T, true>, InitError<'a, $ty<T>, E>>
            where
                A: IntoInit<T, M, Error = E>,
            {
                let init = init.into_init();
                let field_place = unsafe { Uninit::from_raw(self.uninit.as_mut_ptr() as *mut T) };
                match init.init(field_place) {
                    Ok(own) => {
                        mem::forget(own);
                        Ok(
                            unsafe {
                                mem::transmute::<
                                    $unpin<'a, T, false>,
                                    $unpin<'a, T, true>,
                                >(self)
                            },
                        )
                    }
                    Err(err) => Err(self.__err(err.error)),
                }
            }
        }

        impl<'a, T: ?Sized> $unpin<'a, T, true> {
            #[inline]
            #[doc(hidden)]
            pub fn build(self) -> Own<'a, $ty<T>> {
                let this = mem::ManuallyDrop::new(self);
                unsafe {
                    let uninit = core::ptr::read(&this.uninit);
                    uninit.assume_init()
                }
            }
        }

        impl<'a, T: ?Sized + 'a> StructuralInit<'a> for $ty<T> {
            type __BuilderInit = $unpin<'a, T, false>;
            #[inline]
            fn __builder_init(uninit: Uninit<'a, $ty<T>>) -> $unpin<'a, T, false> {
                $unpin { uninit }
            }
        }

        #[doc(hidden)]
        pub struct $pin<'a, 'b, T: ?Sized, const C: bool> {
            uninit: Uninit<'a, $ty<T>>,
            slot: DropSlot<'a, 'b, $ty<T>>,
        }

        impl<'a, 'b, T: ?Sized, const C: bool> $pin<'a, 'b, T, C> {
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
            fn __err<E>(self, err: E) -> InitPinError<'a, 'b, $ty<T>, E> {
                let mut this = mem::ManuallyDrop::new(self);
                unsafe { this.__drop_init() };
                InitPinError {
                    error: err,
                    place: unsafe { core::ptr::read(&this.uninit) },
                    slot: unsafe { core::ptr::read(&this.slot) },
                }
            }
        }

        impl<'a, 'b, T: ?Sized, const C: bool> Drop for $pin<'a, 'b, T, C> {
            #[inline]
            fn drop(&mut self) {
                unsafe { self.__drop_init() };
            }
        }

        impl<'a, 'b, T: ?Sized> $pin<'a, 'b, T, false> {
            #[inline]
            pub fn __next<A, E, M>(
                mut self,
                init: A,
            ) -> Result<$pin<'a, 'b, T, true>, InitPinError<'a, 'b, $ty<T>, E>>
            where
                A: IntoInitPin<T, M, Error = E>,
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
                            $pin { uninit, slot }
                        })
                    }
                    Err(err) => Err(self.__err(err.error)),
                }
            }
        }

        impl<'a, 'b, T: ?Sized> $pin<'a, 'b, T, true> {
            #[inline]
            #[doc(hidden)]
            pub fn build(self) -> POwn<'b, $ty<T>> {
                let this = mem::ManuallyDrop::new(self);
                unsafe {
                    let uninit = core::ptr::read(&this.uninit);
                    let slot = core::ptr::read(&this.slot);
                    uninit.assume_init_pin(slot)
                }
            }
        }

        impl<'b, T: 'b + ?Sized> StructuralInitPin<'b> for $ty<T> {
            type __BuilderInitPin<'a: 'b>
                = $pin<'a, 'b, T, false>
            where
                Self: 'a;

            #[inline]
            fn __builder_init_pin<'a>(
                uninit: Uninit<'a, $ty<T>>,
                slot: DropSlot<'a, 'b, $ty<T>>,
            ) -> $pin<'a, 'b, T, false>
            where
                Self: 'a,
            {
                $pin { uninit, slot }
            }
        }
    )*};
}

derive_value_wrapper! {
    Cell: (InitPinCell, InitCell),
    UnsafeCell: (InitPinUnsafeCell, InitUnsafeCell),
    ManuallyDrop: (InitPinManuallyDrop, InitManuallyDrop),
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
