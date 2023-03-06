//! Provides struct for `Clone` bounds.
use std::any::Any;
use std::hash::Hash;

use dyn_clone::DynClone;

use crate::bounds::{Bounds, ContainerWithHash, HasBounds};

/// Basically dyn trait object for cloneable types
pub trait CloneAny: DynClone + Any {
    fn as_any(&self) -> &dyn Any;
    fn as_mut_any(&mut self) -> &mut dyn Any;
    fn as_box_any(self: Box<Self>) -> Box<dyn Any>;
}

dyn_clone::clone_trait_object!(CloneAny);

impl<T: Clone + Any> CloneAny for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_mut_any(&mut self) -> &mut dyn Any {
        self
    }

    fn as_box_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

/// Clones dyn CloneAny type.
pub fn clone_box<T: ?Sized + CloneAny>(t: &T) -> Box<T> {
    dyn_clone::clone_box(t)
}

/// CloneBounds is used to bound keys or values stored in hashmap to cloneable types.
/// ```rust
/// use std::sync::Arc;
/// use typedmap::{TypedMap, TypedMapKey};
/// use typedmap::clone::{clone_box, CloneBounds};
/// let mut map: TypedMap::<(), CloneBounds, CloneBounds, _> = TypedMap::default();
///
/// #[derive(PartialEq, Eq, Hash, Debug)]
/// struct Key;
///
/// #[derive(Clone, Eq, PartialEq, Hash, Debug)]
/// struct CloneKey;
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// impl TypedMapKey for CloneKey {
///     type Value = u32;
/// }
///
/// map.insert(CloneKey, 32);
/// // Won't compile, because Key is not Clone
/// // map.insert(Key, 32);
///
/// for elem in map.iter() {
///     let cloned = clone_box(elem.key_container_ref());
///     let key = *cloned.as_box_any().downcast::<CloneKey>().unwrap();
///     assert_eq!(key, CloneKey);
///
///     let cloned = clone_box(elem.value_container_ref());
///     let value = *cloned.as_box_any().downcast::<u32>().unwrap();
///     assert_eq!(value, 32);
/// }
/// ```
///
pub struct CloneBounds;

impl Bounds for CloneBounds {
    type KeyContainer = dyn ContainerWithHash<CloneBounds>;
    type Container = dyn CloneAny;

    fn as_any(this: &Self::Container) -> &dyn Any {
        this.as_any()
    }

    fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any {
        this.as_mut_any()
    }

    fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any> {
        this.as_box_any()
    }
}

impl<T: CloneAny> HasBounds<T> for CloneBounds {
    fn cast_box(this: Box<T>) -> Box<Self::Container> {
        this
    }

    fn as_ref(this: &T) -> &Self::Container {
        this
    }

    fn as_mut(this: &mut T) -> &mut Self::Container {
        this
    }

    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        this
    }
}

/// Bounds for Cloneable keys or values which are Send & Sync
pub struct SyncCloneBounds;

impl Bounds for SyncCloneBounds {
    type KeyContainer = dyn ContainerWithHash<SyncCloneBounds> + Send + Sync;
    type Container = dyn CloneAny + Send + Sync;

    fn as_any(this: &Self::Container) -> &dyn Any {
        this.as_any()
    }

    fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any {
        this.as_mut_any()
    }

    fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any> {
        this.as_box_any()
    }
}

impl<T: CloneAny + Send + Sync> HasBounds<T> for SyncCloneBounds {
    fn cast_box(this: Box<T>) -> Box<Self::Container> {
        this
    }

    fn as_ref(this: &T) -> &Self::Container {
        this
    }

    fn as_mut(this: &mut T) -> &mut Self::Container {
        this
    }

    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        this
    }
}
