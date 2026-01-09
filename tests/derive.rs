use std::{cell::Cell, marker::PhantomData};

use placid::*;

#[derive(InitPin, Init)]
struct TestStruct {
    a: u32,
    b: String,
}

#[test]
fn test_build() {
    let pown: POwn<TestStruct> = pown!(init::raw_pin(|uninit, slot| {
        InitPinTestStruct::new(uninit, slot)
            .a(42)
            .unwrap()
            .b(|| String::from("Hello"))
            .unwrap()
            .build()
    }));
    assert_eq!(pown.a, 42);
    assert_eq!(pown.b, "Hello");

    let own: Own<TestStruct> = own!(init::raw(|uninit| {
        InitTestStruct::new(uninit)
            .a(100)
            .unwrap()
            .b(|| String::from("World"))
            .unwrap()
            .build()
    }));
    assert_eq!(own.a, 100);
    assert_eq!(own.b, "World");
}

#[test]
fn test_drop() {
    thread_local! {
        static DROPPED: Cell<bool> = const { Cell::new(false) };
    }

    struct DropTracker;
    impl Drop for DropTracker {
        fn drop(&mut self) {
            DROPPED.set(true);
        }
    }

    #[derive(InitPin, Init)]
    struct TestDrop {
        tracker: DropTracker,
        bomb: u32,
    }

    let t = std::panic::catch_unwind(|| {
        let _: POwn<TestDrop> = pown!(init::raw_pin(|uninit, slot| {
            InitPinTestDrop::new(uninit, slot)
                .tracker(|| DropTracker)
                .unwrap()
                .bomb(|| -> u32 { panic!("Initialization failed") })
                .unwrap()
                .build()
        }));
    });
    t.unwrap_err();
    assert!(DROPPED.replace(false));

    let t = std::panic::catch_unwind(|| {
        let _: Own<TestDrop> = own!(init::raw(|uninit| {
            InitTestDrop::new(uninit)
                .tracker(|| DropTracker)
                .unwrap()
                .bomb(|| -> u32 { panic!("Initialization failed") })
                .unwrap()
                .build()
        }));
    });
    t.unwrap_err();
    assert!(DROPPED.get());
}

#[derive(InitPin, Init)]
pub struct GenericHygiene<Base, Ptr: core::fmt::Debug, Pin>
where
    Pin: Send + Sync + 'static,
{
    base: PhantomData<Base>,
    ptr: PhantomData<Ptr>,
    pub(crate) pin: PhantomData<Pin>,
}
