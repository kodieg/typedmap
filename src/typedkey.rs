use std::any::Any;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::dynhash::{DowncastDynHash, DynHash};
use crate::TypedMapKey;

pub(crate) struct TypedKeyBase<U: AsRef<T>, T>
where
    T: ?Sized + DynHash,
{
    key: U,
    _phantom: PhantomData<T>,
}

impl<U: AsRef<T>, T> Hash for TypedKeyBase<U, T>
where
    T: ?Sized + DynHash,
{
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.key.as_ref().dyn_hash(hasher)
    }
}

impl<U: AsRef<T>, T> PartialEq for TypedKeyBase<U, T>
where
    T: ?Sized + DynHash,
{
    fn eq(&self, other: &Self) -> bool {
        self.key.as_ref().dyn_eq(other.key.as_ref().as_dyn_eq())
    }
}

impl<U: AsRef<T>, T> Eq for TypedKeyBase<U, T> where T: ?Sized + DynHash {}

pub(crate) type TypedKey = TypedKeyBase<Box<dyn DynHash>, dyn DynHash>;
pub(crate) type SyncTypedKey =
    TypedKeyBase<Box<dyn DynHash + Send + Sync>, dyn DynHash + Send + Sync>;

impl TypedKeyBase<Box<dyn DynHash>, dyn DynHash> {
    pub fn from_key<Marker, K: 'static + TypedMapKey<Marker>>(key: K) -> Self {
        Self {
            key: Box::new(key),
            _phantom: PhantomData,
        }
    }
}

impl<U, T> TypedKeyBase<U, T>
where
    U: DowncastDynHash,
    U: AsRef<T>,
    T: ?Sized + DynHash,
{
    pub fn downcast<K: 'static>(self) -> Result<K, Self> {
        self.key
            .downcast::<K>()
            .map(|v| *v)
            .map_err(|key| TypedKeyBase {
                key,
                _phantom: PhantomData,
            })
    }
}

impl<U, T> TypedKeyBase<U, T>
where
    U: AsRef<T>,
    T: ?Sized + DynHash,
{
    pub fn downcast_ref<K: 'static>(&self) -> Option<&K> {
        self.key.as_ref().as_any().downcast_ref::<K>()
    }

    pub fn as_any(&self) -> &dyn Any {
        self.key.as_ref().as_any()
    }
}

impl TypedKeyBase<Box<dyn DynHash + Send + Sync>, dyn DynHash + Send + Sync> {
    pub fn from_key<Marker, K: 'static + TypedMapKey<Marker> + Send + Sync>(key: K) -> Self
    where
        K::Value: Send + Sync,
    {
        Self {
            key: Box::new(key),
            _phantom: PhantomData,
        }
    }
}

pub(crate) trait Key {
    fn key(&self) -> &dyn DynHash;
}

impl<'a> Hash for dyn Key + 'a {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.key().hash(hasher)
    }
}

impl<'a> PartialEq for dyn Key + 'a {
    fn eq(&self, other: &dyn Key) -> bool {
        self.key().eq(other.key())
    }
}

impl<'a> Eq for dyn Key + 'a {}

impl Key for TypedKeyBase<Box<dyn DynHash>, dyn DynHash> {
    fn key(&self) -> &dyn DynHash {
        &*self.key
    }
}

impl Key for TypedKeyBase<Box<dyn DynHash + Send + Sync>, dyn DynHash + Send + Sync> {
    fn key(&self) -> &dyn DynHash {
        &*self.key
    }
}

pub(crate) struct TypedKeyRef<'a> {
    key: &'a dyn DynHash,
}

impl<'a> TypedKeyRef<'a> {
    pub fn from_key_ref<Marker, K: 'static + TypedMapKey<Marker>>(key: &'a K) -> Self {
        Self {
            key: key as &dyn DynHash,
        }
    }
}

impl<'a> Key for TypedKeyRef<'a> {
    fn key(&self) -> &dyn DynHash {
        self.key
    }
}

impl<'a> std::borrow::Borrow<dyn Key + 'a> for TypedKeyBase<Box<dyn DynHash>, dyn DynHash> {
    fn borrow(&self) -> &(dyn Key + 'a) {
        self
    }
}

impl<'a> std::borrow::Borrow<dyn Key + 'a>
    for TypedKeyBase<Box<dyn DynHash + Send + Sync>, dyn DynHash + Send + Sync>
{
    fn borrow(&self) -> &(dyn Key + 'a) {
        self
    }
}
