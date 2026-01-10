use std::{
    cell::UnsafeCell,
    error::Error,
    io::Error as IoError,
    marker::PhantomPinned,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    pin::Pin,
};

use placid::{
    InitPin, POwn, Placed, Uninit,
    init::{InitPinError, IntoInit, try_raw_pin},
    init_pin, pown,
};

pub struct RawMutex {
    lock: UnsafeCell<libc::pthread_mutex_t>,
}

unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

impl Drop for RawMutex {
    fn drop(&mut self) {
        unsafe { libc::pthread_mutex_destroy(self.lock.get()) };
    }
}

impl RawMutex {
    pub const fn new() -> impl InitPin<Self, Error = IoError> {
        try_raw_pin(|mut uninit: Uninit<Self>, slot| {
            let ptr = uninit.as_mut_ptr() as *mut libc::pthread_mutex_t;
            unsafe {
                ptr.write(libc::PTHREAD_MUTEX_INITIALIZER);

                let mut attr = MaybeUninit::uninit();
                let ret = libc::pthread_mutexattr_init(attr.as_mut_ptr());
                if ret != 0 {
                    let error = IoError::from_raw_os_error(ret);
                    return Err(InitPinError::new(error, uninit, slot));
                }

                let ret =
                    libc::pthread_mutexattr_settype(attr.as_mut_ptr(), libc::PTHREAD_MUTEX_NORMAL);
                if ret != 0 {
                    libc::pthread_mutexattr_destroy(attr.as_mut_ptr());
                    let error = IoError::from_raw_os_error(ret);
                    return Err(InitPinError::new(error, uninit, slot));
                }

                let ret = libc::pthread_mutex_init(ptr, attr.as_ptr());
                libc::pthread_mutexattr_destroy(attr.as_mut_ptr());
                if ret != 0 {
                    let error = IoError::from_raw_os_error(ret);
                    return Err(InitPinError::new(error, uninit, slot));
                }

                Ok(uninit.assume_init_pin(slot))
            }
        })
    }

    pub fn lock(&self) -> Result<RawMutexGuard<'_>, IoError> {
        let ret = unsafe { libc::pthread_mutex_lock(self.lock.get()) };
        if ret != 0 {
            return Err(IoError::from_raw_os_error(ret));
        }
        Ok(RawMutexGuard { mutex: self })
    }
}

pub struct RawMutexGuard<'a> {
    mutex: &'a RawMutex,
}

impl<'a> Drop for RawMutexGuard<'a> {
    fn drop(&mut self) {
        unsafe { libc::pthread_mutex_unlock(self.mutex.lock.get()) };
    }
}

#[derive(InitPin)]
pub struct Mutex<T: ?Sized> {
    #[pin]
    raw: RawMutex,
    #[pin]
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T: ?Sized> Mutex<T> {
    pub const fn new<I, M>(data: I) -> impl InitPin<Self, Error = Box<dyn Error>>
    where
        I: IntoInit<T, M, Error: std::error::Error + 'static>,
    {
        init_pin!(
            #[err_into]
            Mutex {
                #[pin]
                raw: RawMutex::new(),
                #[pin]
                data: UnsafeCell(data)
            }
        )
    }

    pub fn lock(&self) -> Result<Pin<MutexGuard<'_, T>>, IoError> {
        let guard = self.raw.lock()?;
        Ok(unsafe {
            Pin::new_unchecked(MutexGuard {
                _guard: guard,
                data: self.data.get(),
            })
        })
    }

    pub fn get_pin_mut(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe { self.map_unchecked_mut(|this| this.data.get_mut()) }
    }
}

pub struct MutexGuard<'a, T: ?Sized> {
    _guard: RawMutexGuard<'a>,
    data: *mut T,
}

impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data }
    }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.data }
    }
}

#[derive(InitPin)]
#[pin_project::pin_project]
struct TestPinned<T>(T, #[pin] PhantomPinned);

#[derive(InitPin)]
#[pin_project::pin_project]
struct TwoMutexes {
    #[pin]
    a: Mutex<u32>,
    #[pin]
    b: Mutex<TestPinned<u32>>,
}

fn main() {
    {
        let m = Mutex::init_pin(Box::new_uninit(), Mutex::new(123));
        println!("{}", *m.lock().unwrap());
        *m.lock().unwrap() = 2;
        println!("{}", *m.lock().unwrap());
        *m.lock().unwrap() = 3;
        println!("{}", *m.lock().unwrap());
    }

    {
        let mut m: POwn<TwoMutexes> = pown!(init_pin!(TwoMutexes {
            a: Mutex::new(0),
            b: Mutex::new(TestPinned(1, PhantomPinned)),
        }));

        println!("{}", *m.a.lock().unwrap());
        *m.a.lock().unwrap() = 2;
        // Use pin-projection to access unpinned fields
        *m.b.lock().unwrap().as_mut().project().0 = 2;
        println!("{}", m.b.lock().unwrap().0);
        // Use pin-projection to access pinned fields.
        *m.as_mut().project().b.get_pin_mut().project().0 = 3;
        println!("{}", m.b.lock().unwrap().0);
    }
}
