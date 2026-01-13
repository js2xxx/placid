use core::{
    fmt,
    mem::{self, ManuallyDrop, MaybeUninit},
    pin::Pin,
};

use crate::{
    init::{Init, InitPin, IntoInit, IntoInitPin},
    owned::Own,
    pin::{DropSlot, DroppingSlot, POwn},
    uninit::Uninit,
};

/// A place slot in memory whose initialization state is tracked at runtime.
///
/// This is similar to [`Option<T>`], but necessary for fallable in-place
/// initialization patterns where `T` does not implement `Default` or `Clone`.
/// For failed initializations, the old value is dropped and the place becomes
/// uninitialized.
///
/// This structure doesn't implement [`Place<T>`] because its initialization
/// state is dynamic and conflicts with the compile-time assertions by
/// `Place<T>`.
///
/// # Examples
///
/// ```rust
/// use placid::{prelude::*, place::DynPlace};
///
/// let mut place: DynPlace<String> = DynPlace::new();
/// assert!(!place.is_init());
///
/// let s = place.insert("Hello".to_string());
/// s.push_str(", world!");
/// assert!(place.is_init());
/// assert_eq!(place.as_deref(), Some("Hello, world!"));
///
/// let s = place.take().unwrap();
/// assert_eq!(s, "Hello, world!");
/// assert!(!place.is_init());
/// ```
///
/// [`Place<T>`]: crate::place::Place
pub struct DynPlace<T> {
    init: bool,
    data: MaybeUninit<T>,
}

impl<T: fmt::Debug> fmt::Debug for DynPlace<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.as_ref() {
            Some(value) => f.debug_tuple("DynPlace").field(value).finish(),
            None => write!(f, "DynPlace(<uninit>)"),
        }
    }
}

impl<T> Default for DynPlace<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynPlace<T> {
    /// Creates a new uninitialized dynamic place.
    #[inline]
    pub const fn new() -> Self {
        Self {
            init: false,
            data: MaybeUninit::uninit(),
        }
    }

    /// Returns `true` if the place is initialized.
    #[inline]
    pub const fn is_init(&self) -> bool {
        self.init
    }

    /// Returns a raw pointer to the value.
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.data.as_ptr()
    }

    /// Returns a mutable raw pointer to the value.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr()
    }

    /// Returns a reference to the value if initialized, or `None` otherwise.
    ///
    /// This is similar to [`Option::as_ref`].
    #[inline]
    pub const fn as_ref(&self) -> Option<&T> {
        if self.init {
            // SAFETY: We checked that the value is initialized.
            Some(unsafe { self.data.assume_init_ref() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value if initialized, or `None`
    /// otherwise.
    ///
    /// This is similar to [`Option::as_mut`].
    #[inline]
    pub const fn as_mut(&mut self) -> Option<&mut T> {
        if self.init {
            // SAFETY: We checked that the value is initialized.
            Some(unsafe { self.data.assume_init_mut() })
        } else {
            None
        }
    }

    /// Returns an owned reference to the value if initialized, or `None`
    /// otherwise.
    ///
    /// The ownership of the value is transferred to the returned `Own<T>`, and
    /// the place becomes uninitialized even if the returned reference gets
    /// [`mem::forget`]ed.
    #[inline]
    pub const fn as_own(&mut self) -> Option<Own<'_, T>> {
        if self.init {
            self.init = false;
            // SAFETY: We checked that the value is initialized.
            Some(unsafe { Own::from_raw(self.data.as_mut_ptr()) })
        } else {
            None
        }
    }

    /// Returns a pinned reference to the value if initialized, or `None`
    /// otherwise.
    ///
    /// This is similar to [`Option::as_pin_ref`].
    #[inline]
    pub const fn as_pin_ref(self: Pin<&Self>) -> Option<Pin<&T>> {
        unsafe {
            // SAFETY: We don't move `data`.
            let this = self.get_ref();
            if this.init {
                // SAFETY: We checked that the value is initialized.
                Some(Pin::new_unchecked(this.data.assume_init_ref()))
            } else {
                None
            }
        }
    }

    /// Returns a pinned mutable reference to the value if initialized, or
    /// `None` otherwise.
    ///
    /// This is similar to [`Option::as_pin_mut`].
    #[inline]
    pub const fn as_pin_mut(self: Pin<&mut Self>) -> Option<Pin<&mut T>> {
        unsafe {
            // SAFETY: We don't move `data`.
            let this = self.get_unchecked_mut();
            if this.init {
                // SAFETY: We checked that the value is initialized.
                Some(Pin::new_unchecked(this.data.assume_init_mut()))
            } else {
                None
            }
        }
    }

    /// Returns a pinned owned reference to the value if initialized, or
    /// `None` otherwise.
    ///
    /// The ownership of the value is transferred to the returned `POwn<T>`, and
    /// the place becomes uninitialized even if the returned reference gets
    /// [`mem::forget`]ed. The value in the place gets properly dropped, as
    /// guaranteed by `slot`.
    #[inline]
    pub fn as_pin_own<'b>(self: Pin<&mut Self>, slot: DropSlot<'_, 'b, T>) -> Option<POwn<'b, T>> {
        // SAFETY: We don't move `data`.
        let this = unsafe { self.get_unchecked_mut() };
        if this.init {
            this.init = false;
            // SAFETY: We checked that the value is initialized.
            Some(unsafe { POwn::new(Own::from_raw(this.data.as_mut_ptr()), slot) })
        } else {
            None
        }
    }

    /// Returns a reference to the dereferenced value if initialized, or
    /// `None` otherwise.
    ///
    /// This is similar to [`Option::as_deref`].
    #[inline]
    pub fn as_deref(&self) -> Option<&T::Target>
    where
        T: core::ops::Deref,
    {
        self.as_ref().map(|r| r.deref())
    }

    /// Returns a mutable reference to the dereferenced value if initialized,
    /// or `None` otherwise.
    ///
    /// This is similar to [`Option::as_deref_mut`].
    #[inline]
    pub fn as_deref_mut(&mut self) -> Option<&mut T::Target>
    where
        T: core::ops::DerefMut,
    {
        self.as_mut().map(|r| r.deref_mut())
    }

    /// Returns a cloned value if initialized, or `None` otherwise.
    ///
    /// This is similar to [`Option::cloned`].
    #[inline]
    pub fn cloned(&self) -> Option<T>
    where
        T: Clone,
    {
        self.as_ref().cloned()
    }

    /// Returns a copied value if initialized, or `None` otherwise.
    ///
    /// This is similar to [`Option::copied`].
    #[inline]
    pub fn copied(&self) -> Option<T>
    where
        T: Copy,
    {
        self.as_ref().copied()
    }

    /// Takes the value out of the place if initialized, leaving it
    /// uninitialized, and returns it. Returns `None` if the place is
    /// uninitialized.
    ///
    /// This is similar to [`Option::take`].
    #[inline]
    pub const fn take(&mut self) -> Option<T> {
        if self.init {
            // SAFETY: We checked that the value is initialized.
            let value = unsafe { self.data.assume_init_read() };
            self.init = false;
            Some(value)
        } else {
            None
        }
    }
}

impl<T> DynPlace<T> {
    /// Drops the value in place if initialized, leaving the place
    /// uninitialized.
    ///
    /// This is a convenience method of `place = DynPlace::new()` for any
    /// `place: DynPlace<T>`.
    pub fn drop_in_place(&mut self) {
        if self.init {
            // SAFETY: We checked that the value is initialized.
            unsafe { self.data.assume_init_drop() };
            self.init = false;
        }
    }

    /// Drops the value in place if initialized, leaving the place
    /// uninitialized.
    ///
    /// This is a convenience method of `place.set(DynPlace::new())` for any
    /// `place: Pin<&mut DynPlace<T>>`.
    pub fn drop_in_place_pin(self: Pin<&mut Self>) {
        // SAFETY: We don't move `data`.
        unsafe { self.get_unchecked_mut().drop_in_place() }
    }

    /// Initializes the place with the given initializer, returning an owned
    /// reference to the value.
    ///
    /// This will drop any existing value in the place regardless of any panic
    /// during initialization.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// let mut s = place.init("Hello".to_string());
    /// s.push_str(", world!");
    /// assert_eq!(*s, "Hello, world!");
    /// drop(s);
    /// assert_eq!(place.as_deref(), None);
    /// ```
    #[inline]
    pub fn init<I, M>(&mut self, init: I) -> Own<'_, T>
    where
        I: IntoInit<T, M>,
    {
        self.try_init(init).unwrap()
    }

    /// Tries to initialize the place with the given initializer, returning an
    /// owned reference to the value.
    ///
    /// This will drop any existing value in the place, regardless of any error
    /// during initialization.
    ///
    /// # Errors
    ///
    /// This will return an error if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// match place.try_init("Hello".to_string()) {
    ///     Ok(mut s) => {
    ///         s.push_str(", world!");
    ///         assert_eq!(*s, "Hello, world!");
    ///     }
    ///     Err(_) => panic!("Initialization failed"),
    /// }
    /// assert_eq!(place.as_deref(), None);
    /// ```
    pub fn try_init<I, M>(&mut self, init: I) -> Result<Own<'_, T>, I::Error>
    where
        I: IntoInit<T, M>,
    {
        self.drop_in_place();

        unsafe {
            let uninit = Uninit::from_raw(self.data.as_mut_ptr());
            init.into_init().init(uninit).map_err(|e| e.error)
        }
    }

    /// Initializes the place with the given initializer if uninitialized,
    /// returning an owned reference to the value.
    ///
    /// See also [`DynPlace::init`], which updates the value regardless of the
    /// initialization state.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    #[inline]
    pub fn get_or_init<I, M>(&mut self, init: I) -> Own<'_, T>
    where
        I: IntoInit<T, M>,
    {
        if self.is_init() {
            self.init = false;
            // SAFETY: We checked that the value is initialized.
            unsafe { Own::from_raw(self.data.as_mut_ptr()) }
        } else {
            self.init(init)
        }
    }

    /// Initializes the pinned place with the given initializer, returning a
    /// pinned mutable reference to the value.
    ///
    /// This will drop any existing value in the place regardless of any panic
    /// during initialization.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace, drop_slot};
    /// use core::pin::pin;
    ///
    /// let mut place = pin!(DynPlace::new());
    /// {
    ///     let slot = drop_slot!();
    ///     let mut s = place.as_mut().init_pin("Hello".to_string(), slot);
    ///     s.push_str(", world!");
    ///     assert_eq!(*s, "Hello, world!");
    /// }
    /// assert_eq!(place.as_deref(), None);
    /// ```
    #[inline]
    pub fn init_pin<'b, I, M>(
        self: Pin<&mut Self>,
        init: I,
        slot: DropSlot<'_, 'b, T>,
    ) -> POwn<'b, T>
    where
        I: IntoInitPin<T, M>,
    {
        self.try_init_pin(init, slot).unwrap()
    }

    /// Tries to initialize the pinned place with the given initializer,
    /// returning a pinned mutable reference to the value.
    ///
    /// This will drop any existing value in the place, regardless of any error
    /// during initialization.
    ///
    /// # Errors
    ///
    /// This will return an error if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace, drop_slot};
    /// use core::pin::pin;
    ///
    /// let mut place = pin!(DynPlace::new());
    /// let slot = drop_slot!();
    /// match place.as_mut().try_init_pin("Hello".to_string(), slot) {
    ///     Ok(mut s) => {
    ///         s.push_str(", world!");
    ///         assert_eq!(*s, "Hello, world!");
    ///     }
    ///     Err(_) => panic!("Initialization failed"),
    /// }
    /// ```
    pub fn try_init_pin<'b, I, M>(
        mut self: Pin<&mut Self>,
        init: I,
        slot: DropSlot<'_, 'b, T>,
    ) -> Result<POwn<'b, T>, I::Error>
    where
        I: IntoInitPin<T, M>,
    {
        self.as_mut().drop_in_place_pin();

        unsafe {
            let this = self.get_unchecked_mut();
            let uninit = Uninit::from_raw(this.data.as_mut_ptr());
            init.into_init().init_pin(uninit, slot).map_err(|e| e.error)
        }
    }

    /// Initializes the pinned place with the given initializer if
    /// uninitialized, returning a pinned mutable reference to the value.
    ///
    /// See also [`DynPlace::init_pin`], which updates the value regardless
    /// of the initialization state.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    #[inline]
    pub fn get_or_init_pin<'b, I, M>(
        self: Pin<&mut Self>,
        init: I,
        slot: DropSlot<'_, 'b, T>,
    ) -> POwn<'b, T>
    where
        I: IntoInitPin<T, M>,
    {
        if self.is_init() {
            // SAFETY: We don't move `data`.
            let this = unsafe { self.get_unchecked_mut() };
            this.init = false;
            // SAFETY: We checked that the value is initialized.
            unsafe { POwn::new(Own::from_raw(this.data.as_mut_ptr()), slot) }
        } else {
            self.init_pin(init, slot)
        }
    }
}

impl<T> DynPlace<T> {
    /// Initializes the place with the given initializer, returning a mutable
    /// reference to the value.
    ///
    /// This is similar to [`Option::insert`], but will drop any existing value
    /// in the place regardless of any panic during initialization.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// let s = place.insert("Hello".to_string());
    /// s.push_str(", world!");
    /// assert_eq!(place.as_deref(), Some("Hello, world!"));
    /// ```
    #[inline]
    pub fn insert<I, M>(&mut self, init: I) -> &mut T
    where
        I: IntoInit<T, M>,
    {
        self.try_insert(init).unwrap()
    }

    /// Tries to initialize the place with the given initializer, returning a
    /// mutable reference to the value.
    ///
    /// This is similar to [`Option::insert`], but will drop any existing value
    /// in the place, regardless of any error during initialization.
    ///
    /// # Errors
    ///
    /// This will return an error if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// match place.try_insert("Hello".to_string()) {
    ///     Ok(s) => {
    ///         s.push_str(", world!");
    ///         assert_eq!(place.as_deref(), Some("Hello, world!"));
    ///     }
    ///     Err(_) => panic!("Initialization failed"),
    /// }
    /// ```
    pub fn try_insert<I, M>(&mut self, init: I) -> Result<&mut T, I::Error>
    where
        I: IntoInit<T, M>,
    {
        mem::forget(self.try_init(init)?);
        self.init = true;
        // SAFETY: We just initialized the value.
        Ok(unsafe { self.data.assume_init_mut() })
    }

    /// Initializes the place with the given initializer if uninitialized,
    /// returning a mutable reference to the value.
    ///
    /// See also [`DynPlace::insert`], which updates the value regardless of the
    /// initialization state.
    ///
    /// This is similar to [`Option::get_or_insert`].
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    #[inline]
    pub fn get_or_insert<I, M>(&mut self, init: I) -> &mut T
    where
        I: IntoInit<T, M>,
    {
        if self.is_init() {
            // SAFETY: We checked that the value is initialized.
            unsafe { self.data.assume_init_mut() }
        } else {
            self.insert(init)
        }
    }

    /// Replaces the value in the place with a new initialized value,
    /// returning the old value if initialized.
    ///
    /// This is similar to [`Option::replace`], but will drop any existing
    /// value in the place regardless of any panic during initialization.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// let old = place.replace("Hello".to_string());
    /// assert!(old.is_none());
    ///
    /// let old = place.replace("World".to_string());
    /// assert_eq!(old, Some("Hello".to_string()));
    ///
    /// assert_eq!(place.as_deref(), Some("World"));
    /// ```
    #[inline]
    pub fn replace<I, M>(&mut self, init: I) -> Option<T>
    where
        I: IntoInit<T, M>,
    {
        self.try_replace(init).unwrap()
    }

    /// Tries to replace the value in the place with a new initialized value,
    /// returning the old value if initialized.
    ///
    /// This is similar to [`Option::replace`], but will drop any existing
    /// value in the place, regardless of any error during initialization.
    ///
    /// # Errors
    ///
    /// This will return an error if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    ///
    /// let mut place: DynPlace<String> = DynPlace::new();
    /// match place.try_replace("Hello".to_string()) {
    ///     Ok(old) => assert!(old.is_none()),
    ///     Err(_) => panic!("Initialization failed"),
    /// }
    /// ```
    #[inline]
    pub fn try_replace<I, M>(&mut self, init: I) -> Result<Option<T>, I::Error>
    where
        I: IntoInit<T, M>,
    {
        let old = self.take();
        self.try_insert(init)?;
        Ok(old)
    }

    /// Initializes the pinned place with the given initializer, returning a
    /// pinned mutable reference to the value.
    ///
    /// This will drop any existing value in the place regardless of any panic
    /// during initialization.
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    /// use core::pin::pin;
    ///
    /// let mut place = pin!(DynPlace::new());
    /// let mut s = place.as_mut().insert_pin("Hello".to_string());
    /// s.push_str(", world!");
    /// assert_eq!(place.as_deref(), Some("Hello, world!"));
    /// ```
    #[inline]
    pub fn insert_pin<I, M>(self: Pin<&mut Self>, init: I) -> Pin<&mut T>
    where
        I: IntoInitPin<T, M>,
    {
        self.try_insert_pin(init).unwrap()
    }

    /// Tries to initialize the pinned place with the given initializer,
    /// returning a pinned mutable reference to the value.
    ///
    /// This will drop any existing value in the place, regardless of any error
    /// during initialization.
    ///
    /// # Errors
    ///
    /// This will return an error if the initialization fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{prelude::*, place::DynPlace};
    /// use core::pin::pin;
    ///
    /// let mut place = pin!(DynPlace::new());
    /// match place.as_mut().try_insert_pin("Hello".to_string()) {
    ///     Ok(mut s) => {
    ///         s.push_str(", world!");
    ///         assert_eq!(place.as_deref(), Some("Hello, world!"));
    ///     }
    ///     Err(_) => panic!("Initialization failed"),
    /// }
    /// ```
    pub fn try_insert_pin<I, M>(mut self: Pin<&mut Self>, init: I) -> Result<Pin<&mut T>, I::Error>
    where
        I: IntoInitPin<T, M>,
    {
        let mut slot = ManuallyDrop::new(DroppingSlot::new());
        // SAFETY: We are not moving the ownership.
        let slot_ref = unsafe { DropSlot::new_unchecked(&mut slot) };
        mem::forget(self.as_mut().try_init_pin(init, slot_ref)?);

        // SAFETY: We don't move `data`.
        let this = unsafe { self.get_unchecked_mut() };
        this.init = true;
        // SAFETY: We just initialized the value.
        Ok(unsafe { Pin::new_unchecked(this.data.assume_init_mut()) })
    }

    /// Initializes the pinned place with the given initializer if
    /// uninitialized, returning a pinned mutable reference to the value.
    ///
    /// See also [`DynPlace::insert_pin`], which updates the value regardless
    /// of the initialization state.
    ///
    /// This is similar to a pinned version of [`Option::get_or_insert`].
    ///
    /// # Panics
    ///
    /// This will panic if the initialization fails.
    #[inline]
    pub fn get_or_insert_pin<I, M>(self: Pin<&mut Self>, init: I) -> Pin<&mut T>
    where
        I: IntoInitPin<T, M>,
    {
        if self.is_init() {
            // SAFETY: We checked that the value is initialized.
            unsafe { Pin::new_unchecked(self.get_unchecked_mut().data.assume_init_mut()) }
        } else {
            self.insert_pin(init)
        }
    }
}

impl<T> Drop for DynPlace<T> {
    fn drop(&mut self) {
        self.drop_in_place();
    }
}
