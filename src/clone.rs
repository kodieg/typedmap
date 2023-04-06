//! Provides struct for `Clone` bounds.
use std::any::Any;
use std::hash::Hash;

use dyn_clone::DynClone;

use crate::bounds::{Bounds, ContainerWithHash, HasBounds};
use crate::impl_custom_bounds;

/// Basically dyn trait object for cloneable types
pub trait CloneAny: DynClone + Any {
    fn as_any(&self) -> &dyn Any;
    fn as_mut_any(&mut self) -> &mut dyn Any;
    fn as_any_box(self: Box<Self>) -> Box<dyn Any>;
}

dyn_clone::clone_trait_object!(CloneAny);

impl<T: Clone + Any> CloneAny for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_mut_any(&mut self) -> &mut dyn Any {
        self
    }

    fn as_any_box(self: Box<Self>) -> Box<dyn Any> {
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
///     let key = *cloned.as_any_box().downcast::<CloneKey>().unwrap();
///     assert_eq!(key, CloneKey);
///
///     let cloned = clone_box(elem.value_container_ref());
///     let value = *cloned.as_any_box().downcast::<u32>().unwrap();
///     assert_eq!(value, 32);
/// }
/// ```
///
pub struct CloneBounds;

/// Bounds for Cloneable keys or values which are Send & Sync
pub struct SyncCloneBounds;
impl_custom_bounds!(CloneBounds, CloneAny, CloneAny);
impl_custom_bounds!(SyncCloneBounds, CloneAny, CloneAny, + Send + Sync);
