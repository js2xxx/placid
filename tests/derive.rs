use std::marker::PhantomData;

use placid::{Own, POwn, init, pown};

#[derive(placid::InitPin, placid::Init)]
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
            .b(String::from("Hello"))
            .unwrap()
            .build()
    }));
    assert_eq!(pown.a, 42);
    assert_eq!(pown.b, "Hello");

    let own: Own<TestStruct> = placid::own!(init::raw(|uninit| {
        InitTestStruct::new(uninit)
            .a(100)
            .unwrap()
            .b(String::from("World"))
            .unwrap()
            .build()
    }));
    assert_eq!(own.a, 100);
    assert_eq!(own.b, "World");
}

#[derive(placid::InitPin, placid::Init)]
pub struct GenericHygiene<Base, Ptr: core::fmt::Debug, Pin>
where
    Pin: Send + Sync + 'static,
{
    base: PhantomData<Base>,
    ptr: PhantomData<Ptr>,
    pub(crate) pin: PhantomData<Pin>,
}
