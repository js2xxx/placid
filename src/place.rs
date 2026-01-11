//! Traits and types for working with places in memory.
//!
//! See the [`Place`] trait for more details.

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, rc::Rc, sync::Arc};
#[cfg(feature = "alloc")]
use core::alloc::Allocator;
use core::{
    fmt,
    marker::{CoercePointee, PhantomData},
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::Deref,
    pin::Pin,
    ptr::{self, NonNull},
};

use self::construct::PlaceConstruct;
use crate::{
    init::{Init, IntoInit},
    owned::Own,
    pin::{DropSlot, POwn},
    sealed,
    uninit::Uninit,
};

/// A place in memory that can hold an owned value of type `T`.
///
/// This trait makes [place expressions] explicit by providing methods to work
/// directly with the underlying memory location. A `Place` can be used to read
/// from or write to the memory location it represents.
///
/// Common types that can be referred to as places include `MaybeUninit<T>`,
/// arrays of `MaybeUninit<T>`, and smart pointers like `Box<MaybeUninit<T>>`,
/// `Rc<MaybeUninit<T>>`, and `Arc<MaybeUninit<T>>`, which is basically a
/// location in heap memory or on the current call stack.
///
/// # Safety
///
/// Implementors of this trait must ensure that the methods uphold their
/// contracts, particularly regarding the initialization state of the memory.
///
/// Specifically:
///
/// - The `as_mut_ptr` method must return a valid pointer to the memory location
///   of the place.
/// - The `assume_init` method must return the same memory location as an
///   initialized place containing a valid value of type `T`. The validity of
///   the place is the caller's responsibility to uphold.
/// - The `from_init` method must correctly wrap an initialized place containing
///   a valid value of type `T` into `Self`, discarding the explicit
///   initialization state. However, the wrapped value must still be valid
///   inside the place.
///
/// [place expressions]: https://doc.rust-lang.org/stable/reference/expressions.html#place-expressions-and-value-expressions
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a place for type `{T}`",
    label = "`{Self}` is not a place for type `{T}`"
)]
pub unsafe trait Place<T: ?Sized>: Sized {
    /// The type of the place, but with an explicit initialized state.
    type Init;

    /// Returns a mutable pointer to the memory location of the place.
    fn as_mut_ptr(&mut self) -> *mut T;

    /// Assumes that the place is initialized and returns the initialized place.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the place is indeed initialized before
    /// calling this method. Failing to do so results in undefined behavior.
    /// See [`MaybeUninit::assume_init`] for more details.
    ///
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    unsafe fn assume_init(self) -> Self::Init;

    /// Discards the explicit initialization state and returns the place.
    fn from_init(init: Self::Init) -> Self;

    /// Initializes the place with the given initializer and returns an owned
    /// reference to the initialized value.
    ///
    /// This method is a convenience method of [`Uninit::from_mut`] +
    /// [`Uninit::write`], allowing direct initialization of a place without
    /// needing to wrap it in an `Uninit` first, which can be directly
    /// type-inferred by the compiler.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    /// use core::mem::MaybeUninit;
    ///
    /// let mut place = MaybeUninit::uninit();
    /// let owned = Place::write(&mut place, 42);
    /// assert_eq!(*owned, 42);
    /// ```
    fn write<'b, M, I>(&'b mut self, init: I) -> Own<'b, T>
    where
        I: IntoInit<T, M, Init: Init<T>, Error: fmt::Debug>,
    {
        Uninit::from_mut(self).write(init)
    }

    /// Initializes the place with the given initializer and returns a pinned
    /// owned reference to the initialized value.
    ///
    /// This method is a convenience method of [`Uninit::from_mut`] +
    /// [`Uninit::write_pin`], allowing direct pinned initialization of a place
    /// without needing to wrap it in an `Uninit` first, which can be directly
    /// type-inferred by the compiler.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{Place, drop_slot};
    /// use core::mem::MaybeUninit;
    ///
    /// let mut place = MaybeUninit::uninit();
    /// let drop_slot = drop_slot!();
    /// let owned = Place::write_pin(&mut place, 42, drop_slot);
    /// assert_eq!(*owned, 42);
    /// ```
    fn write_pin<'a, 'b, M, I>(&'a mut self, init: I, slot: DropSlot<'a, 'b, T>) -> POwn<'b, T>
    where
        I: IntoInit<T, M, Error: fmt::Debug>,
    {
        Uninit::from_mut(self).write_pin(init, slot)
    }

    /// Initializes the place with the given initializer and returns the same
    /// place with an initialized state.
    ///
    /// This method is similar to [`Uninit::write`], but instead of returning an
    /// owned reference, it returns the place itself with an initialized state.
    ///
    /// If type inference fails, use [`Placed::init`] instead.
    ///
    /// # Panics
    ///
    /// This method will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let p = Box::<i32>::new_uninit().init(|| 42);
    /// assert_eq!(*p, 42);
    /// ```
    fn init<M, I, E>(self, init: I) -> Self::Init
    where
        I: IntoInit<T, M, Init: Init<T>, Error = E>,
        E: fmt::Debug,
    {
        self.try_init(init).map_err(|(e, _)| e).unwrap()
    }

    /// Tries to initialize the place with the given initializer and returns
    /// the same place with an initialized state.
    ///
    /// This method is similar to [`Uninit::try_write`], but instead of
    /// returning an owned reference, it returns the place itself with an
    /// initialized state.
    ///
    /// If type inference fails, use [`Placed::try_init`] instead.
    ///
    /// # Errors
    ///
    /// If the initialization fails, this method returns a tuple containing the
    /// error and the original place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let p = Box::<i32>::new_uninit();
    /// let result = p.try_init(|| Ok::<_, &str>(42));
    /// assert!(result.is_ok());
    /// assert_eq!(*result.unwrap(), 42);
    ///
    /// // With a failing initializer
    /// let p = Box::<i32>::new_uninit();
    /// let result = p.try_init(|| Err::<i32, &str>("failed"));
    /// assert!(result.is_err());
    /// ```
    fn try_init<M, I, E>(mut self, init: I) -> Result<Self::Init, (E, Self)>
    where
        I: IntoInit<T, M, Init: Init<T>, Error = E>,
    {
        'ok: {
            let err = match Uninit::from_mut(&mut self).try_write(init) {
                Ok(own) => break 'ok mem::forget(own),
                Err(err) => (mem::forget(err.place), err.error).1,
            };
            return Err((err, self));
        }
        // SAFETY: The place is now initialized, and `own` is forgotten so that the
        // destructor is not run.
        Ok(unsafe { self.assume_init() })
    }

    /// Initializes the place with the given initializer and returns the same
    /// place with a pinned initialized state.
    ///
    /// This method is similar to [`Uninit::write_pin`], but instead of
    /// returning a pinned owned reference, it returns the place itself with
    /// a pinned initialized state.
    ///
    /// If type inference fails, use [`Placed::init_pin`] instead.
    ///
    /// # Panics
    ///
    /// This method will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let place = Box::<i32>::new_uninit().init_pin(|| 42);
    /// assert_eq!(*place, 42);
    /// ```
    fn init_pin<M, I, E>(self, init: I) -> Pin<Self::Init>
    where
        I: IntoInit<T, M, Error = E>,
        Self::Init: Deref,
        E: fmt::Debug,
    {
        self.try_init_pin(init).map_err(|(e, _)| e).unwrap()
    }

    /// Tries to initialize the place with the given initializer and returns the
    /// same place with a pinned initialized state.
    ///
    /// This method is similar to [`Uninit::try_write_pin`], but instead of
    /// returning a pinned owned reference, it returns the place itself with a
    /// pinned initialized state.
    ///
    /// If type inference fails, use [`Placed::try_init_pin`] instead.
    ///
    /// # Errors
    ///
    /// If the initialization fails, this method returns a tuple containing
    /// the error and the original place.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::Place;
    ///
    /// let place = Box::<i32>::new_uninit();
    /// let result = place.try_init_pin(|| Ok::<_, &str>(42));
    /// assert!(result.is_ok());
    /// assert_eq!(*result.unwrap(), 42);
    ///
    /// let place = Box::<i32>::new_uninit();
    /// let result = place.try_init_pin(|| Err::<i32, &str>("failed"));
    /// assert!(result.is_err());
    /// ```
    fn try_init_pin<M, I, E>(mut self, init: I) -> Result<Pin<Self::Init>, (E, Self)>
    where
        I: IntoInit<T, M, Error = E>,
        Self::Init: Deref,
    {
        'ok: {
            let mut slot = ManuallyDrop::new(crate::pin::DroppingSlot::new());
            // SAFETY:
            // - We actually forget `slot` since the lifetime of the object returns back to
            //   the place itself instead of `POwn`.
            let sr = unsafe { crate::pin::DropSlot::new_unchecked(&mut slot) };
            let err = match Uninit::from_mut(&mut self).try_write_pin(init, sr) {
                Ok(own) => break 'ok mem::forget(own),
                Err(err) => (mem::forget((err.place, err.slot)), err.error).1,
            };
            return Err((err, self));
        }
        // SAFETY: The place is now initialized and logically pinned, and `own` & `slot`
        // are forgotten so that the destructor is not run.
        Ok(unsafe { Pin::new_unchecked(self.assume_init()) })
    }
}

pub mod construct;

unsafe impl<T> Place<T> for MaybeUninit<T> {
    type Init = T;

    fn as_mut_ptr(&mut self) -> *mut T {
        self.as_mut_ptr()
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        Self::new(init)
    }
}

unsafe impl<const N: usize> Place<str> for MaybeUninit<[u8; N]> {
    type Init = [u8; N];

    fn as_mut_ptr(&mut self) -> *mut str {
        let ptr = self.as_mut_ptr().cast::<u8>();
        ptr::from_raw_parts_mut(ptr, N)
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.assume_init() }
    }

    fn from_init(init: Self::Init) -> Self {
        MaybeUninit::new(init)
    }
}

unsafe impl<T, U: ?Sized, const N: usize> Place<U> for [MaybeUninit<T>; N]
where
    MaybeUninit<[T; N]>: Place<U>,
{
    type Init = [T; N];

    fn as_mut_ptr(&mut self) -> *mut U {
        // SAFETY: [MaybeUninit<T>; N] and MaybeUninit<[T; N]> have the same memory
        // layout and validity value ranges.
        let r =
            unsafe { mem::transmute::<&mut [MaybeUninit<T>; N], &mut MaybeUninit<[T; N]>>(self) };
        Place::as_mut_ptr(r)
    }

    unsafe fn assume_init(self) -> Self::Init {
        unsafe { self.map(|p| MaybeUninit::assume_init(p)) }
    }

    fn from_init(init: Self::Init) -> Self {
        init.map(MaybeUninit::new)
    }
}

#[cfg(feature = "alloc")]
macro_rules! std_alloc_places {
    ($($ty:ident: [$($mut:ident)?; $($try_slice:ident)?]),* $(,)?) => {
        $(std_alloc_places!(@IMP $ty: [$($mut)?; $($try_slice)?]);)*
    };
    (@IMP $ty:ident: [$($mut:ident)?; $($try_slice:ident)?]) => {
        unsafe impl<T, A: Allocator> Place<T> for $ty<MaybeUninit<T>, A> {
            type Init = $ty<T, A>;

            fn as_mut_ptr(&mut self) -> *mut T {
                std_alloc_places!(@get_mut self, $($mut)? $ty).as_mut_ptr()
            }

            unsafe fn assume_init(self) -> Self::Init {
                unsafe { self.assume_init() }
            }

            fn from_init(init: Self::Init) -> Self {
                let (raw, alloc) = $ty::into_raw_with_allocator(init);
                unsafe { $ty::from_raw_in(raw.cast::<MaybeUninit<T>>(), alloc) }
            }
        }

        impl<T> PlaceConstruct<()> for $ty<T> {
            type Uninit = $ty<MaybeUninit<T>>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(_: ()) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit()
            }
        }

        impl<T, A: Allocator> PlaceConstruct<A> for $ty<T, A> {
            type Uninit = $ty<MaybeUninit<T>, A>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(alloc: A) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit_in(alloc)
            }
        }

        unsafe impl<T, A: Allocator> Place<[T]> for $ty<[MaybeUninit<T>], A> {
            type Init = $ty<[T], A>;

            fn as_mut_ptr(&mut self) -> *mut [T] {
                let len = self.len();
                let ptr = std_alloc_places!(@get_mut self, $($mut)? $ty).as_mut_ptr();
                ptr::from_raw_parts_mut(ptr.cast::<T>(), len)
            }

            unsafe fn assume_init(self) -> Self::Init {
                unsafe { self.assume_init() }
            }

            fn from_init(init: Self::Init) -> Self {
                let len = init.len();
                let (raw, alloc) = $ty::into_raw_with_allocator(init);
                let ptr = std_alloc_places!(@from_raw_parts $($mut)? (
                    raw.cast::<MaybeUninit<T>>(),
                    len,
                ));
                unsafe { $ty::from_raw_in(ptr, alloc) }
            }
        }

        unsafe impl<A: Allocator> Place<str> for $ty<[MaybeUninit<u8>], A> {
            type Init = $ty<str, A>;

            fn as_mut_ptr(&mut self) -> *mut str {
                let len = self.len();
                let ptr = std_alloc_places!(@get_mut self, $($mut)? $ty).as_mut_ptr();
                ptr::from_raw_parts_mut(ptr.cast::<u8>(), len)
            }

            unsafe fn assume_init(self) -> Self::Init {
                unsafe {
                    let (raw, alloc) = $ty::into_raw_with_allocator(self.assume_init());
                    let ptr = std_alloc_places!(@from_raw_parts $($mut)? (
                        raw.cast::<u8>(),
                        raw.len(),
                    ));
                    $ty::from_raw_in(ptr, alloc)
                }
            }

            fn from_init(init: Self::Init) -> Self {
                let len = init.len();
                let (raw, alloc) = $ty::into_raw_with_allocator(init);
                let ptr = std_alloc_places!(@from_raw_parts $($mut)? (
                    raw.cast::<MaybeUninit<u8>>(),
                    len,
                ));
                unsafe { $ty::from_raw_in(ptr, alloc) }
            }
        }

        std_alloc_places!(@TRY_SLICE $($try_slice)? $ty);
    };
    (@get_mut $this:ident, $ty:ident) => {
        $ty::get_mut($this).unwrap()
    };
    (@get_mut $this:ident, mut $ty:ident) => {
        **$this
    };
    (@from_raw_parts ($($t:tt)*)) => {
        ptr::from_raw_parts($($t)*)
    };
    (@from_raw_parts mut ($($t:tt)*)) => {
        ptr::from_raw_parts_mut($($t)*)
    };
    (@TRY_SLICE try_slice $ty:ident) => {
        impl<T> PlaceConstruct<usize> for $ty<[T]> {
            type Uninit = $ty<[MaybeUninit<T>]>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(len: usize) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit_slice(len)
            }
        }

        impl<T, A: Allocator> PlaceConstruct<(usize, A)> for $ty<[T], A> {
            type Uninit = $ty<[MaybeUninit<T>], A>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in((len, alloc): (usize, A)) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit_slice_in(len, alloc)
            }
        }

        impl PlaceConstruct<usize> for $ty<str> {
            type Uninit = $ty<[MaybeUninit<u8>]>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(len: usize) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit_slice(len)
            }
        }

        impl<A: Allocator> PlaceConstruct<(usize, A)> for $ty<str, A> {
            type Uninit = $ty<[MaybeUninit<u8>], A>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in((len, alloc): (usize, A)) -> Result<Self::Uninit, Self::Error> {
                $ty::try_new_uninit_slice_in(len, alloc)
            }
        }
    };
    (@TRY_SLICE $ty:ident) => {
        impl<T> PlaceConstruct<usize> for $ty<[T]> {
            type Uninit = $ty<[MaybeUninit<T>]>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(len: usize) -> Result<Self::Uninit, Self::Error> {
                Ok($ty::new_uninit_slice(len))
            }
        }

        impl<T, A: Allocator> PlaceConstruct<(usize, A)> for $ty<[T], A> {
            type Uninit = $ty<[MaybeUninit<T>], A>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in((len, alloc): (usize, A)) -> Result<Self::Uninit, Self::Error> {
                Ok($ty::new_uninit_slice_in(len, alloc))
            }
        }

        impl PlaceConstruct<usize> for $ty<str> {
            type Uninit = $ty<[MaybeUninit<u8>]>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in(len: usize) -> Result<Self::Uninit, Self::Error> {
                Ok($ty::new_uninit_slice(len))
            }
        }

        impl<A: Allocator> PlaceConstruct<(usize, A)> for $ty<str, A> {
            type Uninit = $ty<[MaybeUninit<u8>], A>;
            type Error = alloc::alloc::AllocError;

            fn try_new_uninit_in((len, alloc): (usize, A)) -> Result<Self::Uninit, Self::Error> {
                Ok($ty::new_uninit_slice_in(len, alloc))
            }
        }
    }
}

#[cfg(feature = "alloc")]
std_alloc_places! {
    Box: [mut; ],
    Rc: [;],
    Arc: [;],
}

/// A place state marker for owned places.
pub enum Owned {}
/// A place state marker for uninitialized places.
pub enum Uninitialized {}

/// A place state marker.
pub trait PlaceState: sealed::Sealed {
    #[doc(hidden)]
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(inner: *mut T);
}

impl sealed::Sealed for Owned {}
impl PlaceState for Owned {
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(inner: *mut T) {
        // SAFETY: The value is owned, so it is initialized.
        unsafe { inner.drop_in_place() };
    }
}

impl sealed::Sealed for Uninitialized {}
impl PlaceState for Uninitialized {
    #[allow(private_interfaces)]
    unsafe fn drop<T: ?Sized>(_inner: *mut T) {
        // No-op, as the value is uninitialized.
    }
}

/// A reference to a place in memory that can hold an owned value of type `T`.
///
/// `PlaceRef` can be in one of two states: [`Owned`] or [`Uninitialized`]. An
/// `Owned` place contains a fully initialized value of type `T`, while an
/// `Uninitialized` place is a location in memory that is reserved for a value
/// of type `T` but has not yet been initialized. The state of the place is
/// tracked at the type level using the `PlaceState` trait.
///
/// Users may find it easier to work with the type aliases [`Own`] and
/// [`Uninit`] instead of using `PlaceRef` directly.
#[derive(CoercePointee)]
#[repr(transparent)]
pub struct PlaceRef<'a, #[pointee] T: ?Sized, State: PlaceState> {
    pub(crate) inner: NonNull<T>,
    state: PhantomData<(State, &'a mut MaybeUninit<PhantomData<T>>)>,
    // See the drop implementation for details on why this is needed.
    owns_value: PhantomData<T>,
}

// General PlaceRef implementations

// SAFETY: PlaceRef is Send if T is Send.
unsafe impl<'a, T: ?Sized + Send, S: PlaceState> Send for PlaceRef<'a, T, S> {}
// SAFETY: PlaceRef is Sync if T is Sync.
unsafe impl<'a, T: ?Sized + Sync, S: PlaceState> Sync for PlaceRef<'a, T, S> {}

impl<'a, T: ?Sized, S: PlaceState> Unpin for PlaceRef<'a, T, S> {}

impl<'a, T: ?Sized, S: PlaceState> PlaceRef<'a, T, S> {
    pub(crate) const unsafe fn from_inner(inner: NonNull<T>) -> Self {
        PlaceRef {
            inner,
            state: PhantomData,
            owns_value: PhantomData,
        }
    }
}

// SAFETY: We have `owns_value: PhantomData<T>`, which tells the dropck that we
// own a value of type T.
unsafe impl<'a, #[may_dangle] T: ?Sized, S: PlaceState> Drop for PlaceRef<'a, T, S> {
    fn drop(&mut self) {
        // SAFETY: We are dropping the place, so we need to drop the value if it is
        // initialized.
        unsafe { S::drop::<T>(self.inner.as_ptr()) };
    }
}

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
    use super::*;
    use crate::{init, place::construct::PlaceStr};

    #[test]
    fn places() {
        let b = Box::new_str(5, init::str("hello"));
        assert_eq!(&*b, "hello");

        let (e, _) = Box::new_uninit_slice(7)
            .try_init(init::str("world"))
            .unwrap_err();
        assert_eq!(e, init::SliceError);
    }
}
