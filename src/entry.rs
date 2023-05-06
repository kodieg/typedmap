//! Entry for TypedMap
use std::marker::PhantomData;

use crate::bounds::{Bounds, HasBounds};
use crate::typedkey::TypedKey;
use crate::typedvalue::TypedMapValue;
use crate::TypedMapKey;

const INVALID_ENTRY: &str = "Broken TypedMap: invalid entry";

pub struct OccupiedEntry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    base: std::collections::hash_map::OccupiedEntry<'a, TypedKey<KB>, TypedMapValue<VB>>,
    _phantom: PhantomData<Marker>,
    _phantom_key: PhantomData<K>,
}

impl<'a, K, KB, VB, Marker> OccupiedEntry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    #[inline]
    pub fn into_mut(self) -> &'a mut K::Value {
        self.base
            .into_mut()
            .downcast_mut::<K::Value>()
            .expect(INVALID_ENTRY)
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

pub struct VacantEntry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    base: std::collections::hash_map::VacantEntry<'a, TypedKey<KB>, TypedMapValue<VB>>,
    _phantom: std::marker::PhantomData<Marker>,
    _phantom_key: std::marker::PhantomData<K>,
}

impl<'a, K, KB, VB, Marker> VacantEntry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
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
    pub fn insert(self, value: K::Value) -> &'a mut K::Value {
        let value = TypedMapValue::from_value(value);
        self.base
            .insert(value)
            .downcast_mut::<K::Value>()
            .expect(INVALID_ENTRY)
    }
}

pub enum Entry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    Occupied(OccupiedEntry<'a, K, KB, VB, Marker>),
    Vacant(VacantEntry<'a, K, KB, VB, Marker>),
}

pub(crate) fn map_entry<Marker, K, KB, VB>(
    entry: std::collections::hash_map::Entry<'_, TypedKey<KB>, TypedMapValue<VB>>,
) -> Entry<'_, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    match entry {
        std::collections::hash_map::Entry::Occupied(base) => Entry::Occupied(OccupiedEntry {
            base,
            _phantom: PhantomData,
            _phantom_key: PhantomData,
        }),
        std::collections::hash_map::Entry::Vacant(base) => Entry::Vacant(VacantEntry {
            base,
            _phantom: PhantomData,
            _phantom_key: PhantomData,
        }),
    }
}

impl<'a, Marker, K, KB, VB> Entry<'a, K, KB, VB, Marker>
where
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    #[inline]
    pub fn or_insert(self, default: K::Value) -> &'a mut K::Value {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> K::Value>(self, default: F) -> &'a mut K::Value {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
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

impl<'a, Marker, K, KB, VB> Entry<'a, K, KB, VB, Marker>
where
    K: 'static,
    K::Value: 'static + Default,
    K: 'static + TypedMapKey<Marker>,
    KB: 'static + Bounds + HasBounds<K>,
    VB: 'static + Bounds + HasBounds<K::Value>,
{
    pub fn or_default(self) -> &'a mut K::Value {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}
