//! Entry type for TypedDashMap
use std::{hash::BuildHasher, marker::PhantomData};

use crate::bounds::{Bounds, HasBounds};
use crate::typedvalue::TypedMapValue;
use crate::TypedMapKey;
use crate::{dashmap::RefMut, typedkey::TypedKey};

const INVALID_ENTRY: &str = "Broken TypedDashMap: invalid entry";

pub struct OccupiedEntry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    base: dashmap::mapref::entry::OccupiedEntry<'a, TypedKey<KB>, TypedMapValue<VB>, S>,
    _phantom: PhantomData<Marker>,
    _phantom_key: PhantomData<K>,
}

impl<'a, K, KB, VB, Marker, S> OccupiedEntry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    #[inline]
    pub fn into_ref(self) -> RefMut<'a, Marker, K, KB, VB, S> {
        let refmut = self.base.into_ref();

        RefMut(refmut, PhantomData, PhantomData)
    }

    #[inline]
    pub fn key(&self) -> &K {
        self.base.key().downcast_ref::<K>().expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn remove_entry(self) -> (K, K::Value) {
        let (k, v) = self.base.remove_entry();
        let v = v.downcast::<K::Value>().expect(INVALID_ENTRY);
        let k = k.downcast::<K>().expect(INVALID_ENTRY);
        (k, v)
    }

    #[inline]
    pub fn get(&self) -> &K::Value {
        self.base
            .get()
            .downcast_ref::<K::Value>()
            .expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut K::Value {
        self.base
            .get_mut()
            .downcast_mut::<K::Value>()
            .expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn insert(&mut self, value: K::Value) -> K::Value {
        let value = TypedMapValue::from_value(value);
        self.base
            .insert(value)
            .downcast::<K::Value>()
            .expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn remove(self) -> K::Value {
        self.base
            .remove()
            .downcast::<K::Value>()
            .expect(INVALID_ENTRY)
    }
}

pub struct VacantEntry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    base: dashmap::mapref::entry::VacantEntry<'a, TypedKey<KB>, TypedMapValue<VB>, S>,
    _phantom: PhantomData<Marker>,
    _phantom_key: PhantomData<K>,
}

impl<'a, K, KB, VB, Marker, S> VacantEntry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    #[inline]
    pub fn key(&self) -> &K {
        self.base.key().downcast_ref::<K>().expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn into_key(self) -> K {
        self.base.into_key().downcast::<K>().expect(INVALID_ENTRY)
    }

    #[inline]
    pub fn insert(self, value: K::Value) -> RefMut<'a, Marker, K, KB, VB, S> {
        let value = TypedMapValue::from_value(value);
        let refmut = self.base.insert(value);

        RefMut(refmut, PhantomData, PhantomData)
    }
}

pub enum Entry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    Occupied(OccupiedEntry<'a, K, KB, VB, Marker, S>),
    Vacant(VacantEntry<'a, K, KB, VB, Marker, S>),
}

pub(crate) fn map_entry<Marker, K, KB, VB, S>(
    entry: dashmap::mapref::entry::Entry<'_, TypedKey<KB>, TypedMapValue<VB>, S>,
) -> Entry<'_, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
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

impl<'a, Marker, K, KB, VB, S> Entry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    #[inline]
    pub fn or_insert(self, default: K::Value) -> RefMut<'a, Marker, K, KB, VB, S> {
        match self {
            Self::Occupied(entry) => entry.into_ref(),
            Self::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> K::Value>(
        self,
        default: F,
    ) -> RefMut<'a, Marker, K, KB, VB, S> {
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

impl<'a, Marker, K, KB, VB, S> Entry<'a, K, KB, VB, Marker, S>
where
    K: 'static + TypedMapKey<Marker>,
    K::Value: 'static + Default,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
    S: BuildHasher,
{
    pub fn or_default(self) -> RefMut<'a, Marker, K, KB, VB, S> {
        match self {
            Self::Occupied(entry) => entry.into_ref(),
            Self::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}
