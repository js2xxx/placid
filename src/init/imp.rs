use core::{
    cell::{Cell, UnsafeCell},
    marker::{PhantomData, PhantomPinned},
    mem::{self, ManuallyDrop},
    ptr::NonNull,
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
            pub fn __build(self) -> Fix<Own<'a, $ty<T>>> {
                let this = mem::ManuallyDrop::new(self);
                unsafe {
                    let uninit = core::ptr::read(&this.uninit);
                    Fix::new(uninit.assume_init())
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
            pub fn __build(self) -> POwn<'b, $ty<T>> {
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
    pub fn __build(self) -> Fix<Own<'a, PhantomPinned>> {
        unsafe { Fix::new(self.uninit.assume_init()) }
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
    pub fn __build(self) -> POwn<'b, PhantomPinned> {
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

#[doc(hidden)]
pub struct InitPhantomData<'a, T: ?Sized> {
    uninit: Uninit<'a, PhantomData<T>>,
}

impl<'a, T: ?Sized> InitPhantomData<'a, T> {
    #[inline]
    #[doc(hidden)]
    pub fn __build(self) -> Fix<Own<'a, PhantomData<T>>> {
        unsafe { Fix::new(self.uninit.assume_init()) }
    }
}

impl<'a, T: ?Sized + 'a> StructuralInit<'a> for PhantomData<T> {
    type __BuilderInit = InitPhantomData<'a, T>;
    #[inline]
    fn __builder_init(uninit: Uninit<'a, PhantomData<T>>) -> InitPhantomData<'a, T> {
        InitPhantomData { uninit }
    }
}

#[doc(hidden)]
pub struct InitPinPhantomData<'a, 'b, T: ?Sized> {
    uninit: Uninit<'a, PhantomData<T>>,
    slot: DropSlot<'a, 'b, PhantomData<T>>,
}

impl<'a, 'b, T: ?Sized> InitPinPhantomData<'a, 'b, T> {
    #[inline]
    #[doc(hidden)]
    pub fn __build(self) -> POwn<'b, PhantomData<T>> {
        unsafe { self.uninit.assume_init_pin(self.slot) }
    }
}

impl<'b, T: ?Sized> StructuralInitPin<'b> for PhantomData<T> {
    type __BuilderInitPin<'a: 'b>
        = InitPinPhantomData<'a, 'b, T>
    where
        Self: 'a;

    #[inline]
    fn __builder_init_pin<'a>(
        uninit: Uninit<'a, PhantomData<T>>,
        slot: DropSlot<'a, 'b, PhantomData<T>>,
    ) -> InitPinPhantomData<'a, 'b, T>
    where
        Self: 'a,
    {
        InitPinPhantomData { uninit, slot }
    }
}

/// The pointer to the place being initialized.
///
/// This struct represents a pointer to the place being initialized, which
/// appears in [structural initializers](crate::init::init) as `this`.
/// It can be used to construct self-referential pointers in the place being
/// initialized.
///
/// It can be safely destructured by [`munge`].
pub struct ThisPtr<'a, T: ?Sized> {
    ptr: NonNull<T>,
    extent: NonNull<[u8]>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T: ?Sized> Clone for ThisPtr<'a, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<'a, T: ?Sized> Copy for ThisPtr<'a, T> {}

impl<'a, T: ?Sized> ThisPtr<'a, T> {
    /// Constructs a new `ThisPtr` from a raw pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    /// - `ptr` points to the place being initialized and it is valid for the
    ///   duration of the initialization (e.g., it has a valid metadata if `T`
    ///   is a DST);
    /// - the returned pointer doesn't escape the initialization scope, e.g. by
    ///   being stored in a static variable or being returned from the
    ///   initializer.
    #[inline]
    pub const unsafe fn new_unchecked(ptr: NonNull<T>) -> Self {
        let base = ptr.cast::<u8>();
        // SAFETY: The caller ensures that `base` has a valid metadata.
        let size = unsafe { core::mem::size_of_val_raw(ptr.as_ptr()) };

        Self {
            ptr,
            extent: NonNull::slice_from_raw_parts(base, size),
            _marker: PhantomData,
        }
    }

    #[inline]
    #[doc(hidden)]
    pub const unsafe fn new_scoped(ptr: NonNull<T>, scope: &'a mut ()) -> Self {
        let _ = scope;
        unsafe { Self::new_unchecked(ptr) }
    }

    /// Retrieves the raw pointer to be initialized.
    ///
    /// # Safety
    ///
    /// This function is safe to call, but the caller must treat the returned
    /// pointer as immutable and must not allow it to escape the initialization
    /// scope.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub const fn as_ptr(self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Retrieves the non-null pointer to be initialized.
    ///
    /// # Safety
    ///
    /// This function is safe to call, but the caller must treat the returned
    /// pointer as immutable and must not allow it to escape the initialization
    /// scope.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub const fn as_non_null(self) -> NonNull<T> {
        self.ptr
    }

    /// Retrieves the memory region of the target place that contains the
    /// pointer to be initialized.
    #[inline]
    pub const fn extent(self) -> NonNull<[u8]> {
        self.extent
    }
}

unsafe impl<'a, T: ?Sized> munge::Destructure for ThisPtr<'a, T> {
    type Underlying = T;

    type Destructuring = munge::Move;

    #[inline]
    fn underlying(&mut self) -> *mut Self::Underlying {
        self.as_ptr()
    }
}

unsafe impl<'a, T: ?Sized, U: ?Sized> munge::Restructure<U> for ThisPtr<'a, T> {
    type Restructured = ThisPtr<'a, U>;

    #[inline]
    unsafe fn restructure(&self, ptr: *mut U) -> Self::Restructured {
        ThisPtr {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            extent: self.extent,
            _marker: PhantomData,
        }
    }
}
