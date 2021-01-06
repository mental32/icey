//! Dynamically (at const time) sized, Stack allocated, Trait Objects.
//!
//! As a great man once said:
//!
//! > The curse density in this is impressive.
//!
//! Here have a ~~cookie~~ example:
//! ```
//! # use icey::*;
//!
//! fn main() {
//!     let value = 0;
//!     let obj =
//!         trait_object::<dyn Fn() -> String, _>(move || format!("Hello there! value={}", value));
//!
//!     let v = {
//!         let a = obj.as_ref();
//!
//!         let b = obj.as_ref();
//!
//!         // let c = obj.as_mut();  // ERROR ~ 'already borrowed: BorrowMutError'
//!
//!         (a(), b())
//!     };
//!
//!     eprintln!("{:?}", v);
//! }
//! ```

#![feature(const_evaluatable_checked)]
#![feature(const_generics)]
#![feature(unsize)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(
    feature = "const_fn",
    feature(
        const_fn,
        const_refs_to_cell,
        const_fn_fn_ptr_basics,
        const_panic,
        const_intrinsic_copy,
        const_slice_from_raw_parts,
        const_maybe_uninit_assume_init,
        const_raw_ptr_deref,
        const_raw_ptr_to_usize_cast,
        const_mut_refs
    )
)]

use core::cell::{Ref, RefCell, RefMut};
use core::intrinsics::copy_nonoverlapping;
use core::marker::PhantomData;
use core::marker::Unsize;
use core::mem::ManuallyDrop;
use core::mem::{align_of, forget, size_of, MaybeUninit};
use core::ptr;
use core::slice;

/// Makes a function const only when `feature = "const_fn"` is enabled.
macro_rules! const_fn {
    (
        $(#[$attr:meta])*
        $sv:vis fn $($fn:tt)*
    ) => {
        $(#[$attr])*
        #[cfg(feature = "const_fn")]
        $sv const fn $($fn)*

        $(#[$attr])*
        #[cfg(not(feature = "const_fn"))]
        $sv fn $($fn)*
    };
    (
        $(#[$attr:meta])*
        $sv:vis unsafe fn $($fn:tt)*
    ) => {
        $(#[$attr])*
        #[cfg(feature = "const_fn")]
        $sv const unsafe fn $($fn)*

        $(#[$attr])*
        #[cfg(not(feature = "const_fn"))]
        $sv unsafe fn $($fn)*
    };
}

const_fn! {
    /// Create a `TraitObject` from a value of `U` that dereferences into `T`.
    #[inline]
    pub fn trait_object<T, U>(val: U) -> TraitObject<T, { size_of::<U>() }>
    where
        T: ?Sized,
        U: Unsize<T>,
    {
        // SAFETY: We're manually providing the correct size of the underlying erased buffer.
        unsafe { TraitObject::<T, { size_of::<U>() }>::new(val) }
    }
}

// -- TypeErasedObject

/// A generically sized struct capable of storing `N` bytes.
///
/// Used to store some erased `T`.
#[repr(align(16))]
pub(crate) struct TypeErasedObject<const N: usize> {
    pub(crate) buf: [u8; N],
}

impl<const N: usize> TypeErasedObject<N> {
    const_fn! {
        pub(crate) unsafe fn new<U>(val: ManuallyDrop<U>) -> Self {
            #[cfg(not(feature = "const_fn"))]
            assert!(align_of::<U>() <= 16);

            #[cfg(not(feature = "const_fn"))]
            assert!(
                N == size_of::<U>(),
                "`obj` of size `N`({:?} bytes) must match `U` ({:?} bytes)...",
                N,
                size_of::<U>()
            );

            let mut obj = MaybeUninit::<TypeErasedObject<N>>::uninit().assume_init();

            copy_nonoverlapping(&val as *const ManuallyDrop<U> as *const U, &mut obj as *const _ as *mut U, 1);

            forget(val);

            obj
        }
    }
}

pub(crate) struct UnsafeTraitObject<T: ?Sized, const N: usize> {
    inner: TypeErasedObject<N>,
    vtable_ptr: usize,
    _phantom: PhantomData<T>,
}

impl<T: ?Sized, const N: usize> UnsafeTraitObject<T, N> {
    const_fn! {
        pub(crate) unsafe fn new<U>(val: U) -> Self
        where
            U: Unsize<T> {
                let obj = TypeErasedObject::new(ManuallyDrop::new(val));
                let val = &*(&obj as *const _ as *const U);

                let mut t_ptr: *const T = val as &T;
                let (data_ptr, vtable_ptr) = {
                    let ptr = &mut t_ptr;

                    let fat_ptr = {
                        let data = ptr as *mut *const T as *mut usize;
                        let len = size_of::<*mut T>() / size_of::<usize>();
                        unsafe { &mut *ptr::slice_from_raw_parts_mut(data, len) }
                    };

                    #[cfg(not(feature = "const_fn"))]
                    assert_eq!(
                        fat_ptr.len(),
                        2,
                        "The layout of TraitObjects is unstable and this was written with a (data_ptr, vtable_ptr) layout in mind,\
                        unfortunately that does not appear to be the case here..."
                    );

                    (fat_ptr[0], fat_ptr[1])
                };

                #[cfg(not(feature = "const_fn"))]
                assert_eq!(
                    data_ptr, val as *const _ as usize,
                    "Expected the first word of the generated fat_ptr to be the address of val."
                );

                Self {
                    inner: obj,
                    vtable_ptr,
                    _phantom: PhantomData,
                }
            }
    }

    pub(crate) unsafe fn as_fat_ptr(&self) -> *const T {
        let data_ptr = self.inner.buf.as_ptr() as usize;

        let mut rv = MaybeUninit::<*mut T>::uninit();

        let fat_ptr = slice::from_raw_parts_mut(
            (&mut rv) as *mut _ as *mut usize,
            size_of::<*mut T>() / size_of::<usize>(),
        );

        fat_ptr[0] = data_ptr;
        fat_ptr[1] = self.vtable_ptr;

        rv.assume_init()
    }
}

// -- TraitObject

/// A trait object layout that stores the underlying "object" with the `vtable_ptr`.
pub struct TraitObject<T: ?Sized, const N: usize> {
    inner: RefCell<UnsafeTraitObject<T, N>>,
}

impl<T: ?Sized, const N: usize> TraitObject<T, N> {
    const_fn! {
        pub(crate) unsafe fn new<U>(val: U) -> Self
        where
            U: Unsize<T>,
        {
            Self {
                inner: RefCell::new(UnsafeTraitObject::new(val)),
            }
        }
    }

    pub fn as_ref(&self) -> Ref<'_, T> {
        Ref::map(self.inner.borrow(), |to| unsafe {
            &*(to.as_fat_ptr() as *const _) // TODO: `as *const _` is needed to compile succesfully for whatever reason.
        })
    }

    pub fn as_mut(&self) -> RefMut<'_, T> {
        RefMut::map(self.inner.borrow_mut(), |to| unsafe {
            &mut *(to.as_fat_ptr() as *mut _)
        })
    }
}

#[cfg(test)]
#[cfg_attr(test, test)]
#[should_panic(expected = "already borrowed: BorrowMutError")]
fn why_does_this_ice() {
    let value = 0;
    let obj =
        trait_object::<dyn Fn() -> String, _>(move || format!("Hello there! value={}", value));

    let a = obj.as_ref();

    let b = obj.as_ref();

    let _ = obj.as_mut(); // ERROR ~ 'already borrowed: BorrowMutError'

    let _ = (a(), b());
}

#[cfg(test)]
#[cfg_attr(test, test)]
fn const_might_ice_idk() {
    #[cfg(feature = "const_fn")]
    {
        const OBJECT: TraitObject<dyn core::fmt::Debug, { size_of::<usize>() }> =
            trait_object(123456789_usize);
        eprintln!("{:?}", OBJECT.as_ref());
    }
}
