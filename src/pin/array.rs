use core::{mem, ptr::NonNull};

use crate::pin::POwn;

impl<'a, T, const N: usize> POwn<'a, [T; N]> {
    /// Returns the number of elements in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = pown!([1, 2, 3]);
    /// assert_eq!(arr.len(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        N
    }

    /// Returns `true` if the slice contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let empty_arr: POwn<[i32; 0]> = pown!([]);
    /// assert!(empty_arr.is_empty());
    ///
    /// let non_empty_arr = pown!([1, 2, 3]);
    /// assert!(!non_empty_arr.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        N == 0
    }

    /// Converts the pinned & owned array into a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let array: POwn<[i32; 3]> = pown!([1, 2, 3]);
    /// let slice: POwn<[i32]> = array.into_slice();
    /// assert_eq!(*slice, [1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn into_slice(self) -> POwn<'a, [T]> {
        let drop_flag = self.drop_flag;
        let inner = self.inner;
        mem::forget(self);

        let slice_ptr = inner.cast::<T>();
        let slice_slice_ptr = NonNull::slice_from_raw_parts(slice_ptr, N);

        POwn {
            drop_flag,
            inner: slice_slice_ptr,
        }
    }
}
