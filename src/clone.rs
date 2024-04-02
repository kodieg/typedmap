//! Provides struct for `Clone` bounds.
use std::any::Any;

use dyn_clone::DynClone;

use crate::bounds::{Bounds, ContainerWithHash};
use crate::{impl_custom_bounds_with_key_container, TypedMap};

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

pub trait ContainerWithHashAndClone<B: Bounds>: ContainerWithHash<B> + CloneAny {}

impl<B: Bounds, K: ContainerWithHash<B> + CloneAny + 'static> ContainerWithHashAndClone<B> for K {}

/// Bounds for Cloneable keys or values which are Send & Sync
pub struct SyncCloneBounds;
impl_custom_bounds_with_key_container!(
    CloneBounds,
    CloneAny,
    dyn ContainerWithHashAndClone<CloneBounds>,
    CloneAny
);
impl_custom_bounds_with_key_container!(
    SyncCloneBounds,
    CloneAny,
    dyn ContainerWithHashAndClone<SyncCloneBounds> + Send + Sync,
    CloneAny, + Send + Sync
);

impl<M, KB: 'static + Bounds, VB: 'static + Bounds> Clone for TypedMap<M, KB, VB>
where
    KB::KeyContainer: CloneAny,
    VB::Container: CloneAny,
{
    fn clone(&self) -> Self {
        self.iter().map(|pair| pair.to_owned()).collect()
    }
}

#[cfg(feature = "dashmap")]
impl<M, KB: 'static + Bounds, VB: 'static + Bounds> Clone for crate::TypedDashMap<M, KB, VB>
where
    KB::KeyContainer: CloneAny,
    VB::Container: CloneAny,
{
    fn clone(&self) -> Self {
        self.iter().map(|pair| pair.to_owned()).collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::clone::{CloneBounds, SyncCloneBounds};

    use crate::TypedMap;
    use crate::TypedMapKey;

    struct Marker;

    impl TypedMapKey<Marker> for String {
        type Value = String;
    }

    #[test]
    fn test_clone_typed_map() {
        let mut map: TypedMap<Marker, CloneBounds, SyncCloneBounds> = TypedMap::new_with_bounds();
        map.insert("String".to_owned(), "Value".to_owned());

        let map2 = map.clone();
        assert_eq!(map2.get(&"String".to_owned()), Some(&"Value".to_owned()))
    }

    #[cfg(feature = "dashmap")]
    #[test]
    fn test_clone() {
        use crate::clone::SyncCloneBounds;
        use crate::TypedDashMap;
        let state: TypedDashMap<Marker, SyncCloneBounds, SyncCloneBounds> =
            TypedDashMap::new_with_bounds();
        state.insert("Key".to_owned(), "Value".to_owned());

        let cloned = state.clone();
        assert_eq!(
            state.get(&"Key".to_owned()).unwrap().value(),
            cloned.get(&"Key".to_owned()).unwrap().value()
        );
    }
}
