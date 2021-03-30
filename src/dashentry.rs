use std::{hash::BuildHasher, marker::PhantomData};

use crate::typedvalue::SyncTypedMapValue;
use crate::TypedMapKey;
use crate::{dashmap::RefMut, typedkey::SyncTypedKey};

pub struct OccupiedEntry<'a, K, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: Send + Sync,
    S: BuildHasher,
{
    base: dashmap::mapref::entry::OccupiedEntry<'a, SyncTypedKey, SyncTypedMapValue, S>,
    _phantom: std::marker::PhantomData<Marker>,
    _phantom_key: std::marker::PhantomData<K>,
}

impl<'a, K, Marker, S> OccupiedEntry<'a, K, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: Send + Sync,
    S: BuildHasher,
{
    #[inline]
    pub fn into_ref(self) -> RefMut<'a, Marker, K, S> {
        let refmut = self.base.into_ref();

        RefMut(refmut, PhantomData, PhantomData)
    }

    #[inline]
    pub fn key(&self) -> &K {
        self.base
            .key()
            .downcast_ref::<K>()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn remove_entry(self) -> (K, K::Value) {
        let (k, v) = self.base.remove_entry();
        let v = v.downcast::<K::Value>().expect("Broken TypedMap entry");
        let k = k.downcast::<K>().ok().expect("Broken TypedMap entry");
        (k, v)
    }

    #[inline]
    pub fn get(&self) -> &K::Value {
        self.base
            .get()
            .downcast_ref::<K::Value>()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut K::Value {
        self.base
            .get_mut()
            .downcast_mut::<K::Value>()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn insert(&mut self, value: K::Value) -> K::Value {
        let value = SyncTypedMapValue::from_value(value);
        self.base
            .insert(value)
            .downcast::<K::Value>()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn remove(self) -> K::Value {
        self.base
            .remove()
            .downcast::<K::Value>()
            .expect("Broken TypedMap entry")
    }
}

pub struct VacantEntry<'a, K, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: Send + Sync,
    S: BuildHasher,
{
    base: dashmap::mapref::entry::VacantEntry<'a, SyncTypedKey, SyncTypedMapValue, S>,
    _phantom: std::marker::PhantomData<Marker>,
    _phantom_key: std::marker::PhantomData<K>,
}

impl<'a, K, Marker, S> VacantEntry<'a, K, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: Send + Sync,
    S: BuildHasher,
{
    #[inline]
    pub fn key(&self) -> &K {
        self.base
            .key()
            .downcast_ref::<K>()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn into_key(self) -> K {
        self.base
            .into_key()
            .downcast::<K>()
            .ok()
            .expect("Broken TypedMap entry")
    }

    #[inline]
    pub fn insert(self, value: K::Value) -> RefMut<'a, Marker, K, S> {
        let value = SyncTypedMapValue::from_value(value);
        let refmut = self.base.insert(value);

        RefMut(refmut, PhantomData, PhantomData)
    }
}

pub enum Entry<'a, K, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: Send + Sync,
    S: BuildHasher,
{
    Occupied(OccupiedEntry<'a, K, Marker, S>),
    Vacant(VacantEntry<'a, K, Marker, S>),
}

pub(crate) fn map_entry<Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher>(
    entry: dashmap::mapref::entry::Entry<'_, SyncTypedKey, SyncTypedMapValue, S>,
) -> Entry<'_, K, Marker, S>
where
    K::Value: Send + Sync,
{
    match entry {
        dashmap::mapref::entry::Entry::Occupied(base) => Entry::Occupied(OccupiedEntry {
            base,
            _phantom: PhantomData,
            _phantom_key: PhantomData,
        }),
        dashmap::mapref::entry::Entry::Vacant(base) => Entry::Vacant(VacantEntry {
            base,
            _phantom: PhantomData,
            _phantom_key: PhantomData,
        }),
    }
}

impl<'a, Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher> Entry<'a, K, Marker, S>
where
    K::Value: Send + Sync,
{
    #[inline]
    pub fn or_insert(self, default: K::Value) -> RefMut<'a, Marker, K, S> {
        match self {
            Self::Occupied(entry) => entry.into_ref(),
            Self::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> K::Value>(self, default: F) -> RefMut<'a, Marker, K, S> {
        match self {
            Self::Occupied(entry) => entry.into_ref(),
            Self::Vacant(entry) => entry.insert(default()),
        }
    }

    pub fn key(&self) -> &K {
        match *self {
            Self::Occupied(ref entry) => entry.key(),
            Self::Vacant(ref entry) => entry.key(),
        }
    }

    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut K::Value),
    {
        match self {
            Self::Occupied(mut entry) => {
                f(entry.get_mut());
                Self::Occupied(entry)
            }
            Self::Vacant(entry) => Self::Vacant(entry),
        }
    }
}

impl<'a, Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher> Entry<'a, K, Marker, S>
where
    K::Value: Default,
    K::Value: Send + Sync,
{
    pub fn or_default(self) -> RefMut<'a, Marker, K, S> {
        match self {
            Self::Occupied(entry) => entry.into_ref(),
            Self::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}
