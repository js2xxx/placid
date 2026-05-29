use core::mem::{self, MaybeUninit};

use crate::place::{PlaceRef, PlaceState};

impl<'a, T, const N: usize, S: PlaceState> PlaceRef<'a, [T; N], S> {
    /// Returns the length of the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = own!([1, 2, 3]);
    /// assert_eq!(arr.len(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        N
    }

    /// Returns `true` if the array is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = own!([1, 2, 3]);
    /// assert!(!arr.is_empty());
    ///
    /// let empty_arr: Own<[i32; 0]> = own!([]);
    /// assert!(empty_arr.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        N == 0
    }

    /// Converts the array place into a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = own!([1, 2, 3]);
    /// let slice = arr.to_slice();
    /// assert_eq!(*slice, [1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_slice(self) -> PlaceRef<'a, [T], S> {
        self
    }

    /// Converts the array place into an array of places, one for each element.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = own!([1, 2, 3]);
    /// let places = arr.to_each();
    /// assert_eq!(places.map(|p| *p), [1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_each(self) -> [PlaceRef<'a, T, S>; N] {
        let inner = self.inner.cast::<T>();
        mem::forget(self);

        let mut ret: [MaybeUninit<PlaceRef<'a, T, S>>; N] = [const { MaybeUninit::uninit() }; N];
        let mut i = 0;
        while i < N {
            // SAFETY: We are writing to the `i`-th element of `ret`, which is valid because
            // `i < N`.
            ret[i].write(unsafe { PlaceRef::from_inner(inner.add(i)) });
            i += 1;
        }
        // SAFETY: We have just initialized all elements of `ret`; `MaybeUninit<Q>` is
        // `repr(transparent)` over `Q`, so the transmuting is sound.
        unsafe { mem::transmute_copy(&ret) }
    }
}

/// The methods derived from slices are implemented in [mod@super::slice].
type _Fwd = ();
