use std::any::Any;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

use crate::bounds::{Bounds, ContainerWithHash, HasBounds};
use crate::dynhash::DynHash;

pub(crate) struct TypedKey<B: Bounds>(pub(crate) Box<B::KeyContainer>);

impl<B: Bounds> Hash for TypedKey<B> {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        self.0.as_dyn_hash().dyn_hash(hasher)
    }
}

impl<B: Bounds> PartialEq for TypedKey<B> {
    fn eq(&self, other: &Self) -> bool {
        self.0
            .as_dyn_hash()
            .dyn_eq(other.0.as_dyn_hash().as_dyn_eq())
    }
}

impl<B: Bounds> Eq for TypedKey<B> {}

impl<B: 'static + Bounds> Debug for TypedKey<B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("TypedKey")
    }
}

impl<B: 'static + Bounds> TypedKey<B> {
    pub fn downcast<K: 'static>(self) -> Result<K, Self>
    where
        B: HasBounds<K>,
    {
        if self.is::<K>() {
            Ok(*B::downcast_box(self.0.into_box_container())
                .unwrap_or_else(|_| panic!("downcast failed")))
        } else {
            Err(self)
        }
    }

    pub fn downcast_ref<K: 'static>(&self) -> Option<&K>
    where
        B: HasBounds<K>,
    {
        B::downcast_ref(self.0.as_container())
    }

    pub fn as_any(&self) -> &dyn Any {
        self.0.as_dyn_hash().as_any()
    }

    pub fn is<K: 'static>(&self) -> bool {
        B::as_any(self.0.as_container()).is::<K>()
    }

    pub fn from_key<K: 'static + Hash + Eq>(key: K) -> TypedKey<B>
    where
        B: HasBounds<K>,
    {
        TypedKey(B::box_key(key))
    }

    pub fn as_container(&self) -> &B::Container {
        self.0.as_container()
    }

    pub fn as_mut_container(&mut self) -> &mut B::Container {
        self.0.as_mut_container()
    }

    pub fn into_box_container(self) -> Box<B::Container> {
        self.0.into_box_container()
    }
}

pub(crate) trait Key {
    fn key(&self) -> &dyn DynHash;
}

impl Hash for dyn Key + '_ {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.key().hash(hasher)
    }
}

impl PartialEq for dyn Key + '_ {
    fn eq(&self, other: &dyn Key) -> bool {
        self.key().eq(other.key())
    }
}

impl Eq for dyn Key + '_ {}

impl<B: Bounds> Key for TypedKey<B> {
    fn key(&self) -> &dyn DynHash {
        self.0.as_dyn_hash()
    }
}

pub(crate) struct TypedKeyRef<'a> {
    key: &'a dyn DynHash,
}

impl<'a> TypedKeyRef<'a> {
    pub fn from_key_ref<K: 'static + Hash + Eq>(key: &'a K) -> Self {
        Self {
            key: key as &dyn DynHash,
        }
    }
}

impl Key for TypedKeyRef<'_> {
    fn key(&self) -> &dyn DynHash {
        self.key
    }
}

impl<'a, B: Bounds + 'a> std::borrow::Borrow<dyn Key + 'a> for TypedKey<B> {
    fn borrow(&self) -> &(dyn Key + 'a) {
        self
    }
}
