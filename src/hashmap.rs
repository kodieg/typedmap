use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};
use std::iter::FusedIterator;
use std::{any::Any, fmt::Debug, ops::Index};
use std::{collections::hash_map::RandomState, marker::PhantomData};

use crate::entry;
use crate::typedkey::{Key, TypedKey, TypedKeyRef};
use crate::typedvalue::TypedMapValue;

/// A trait that a key stored in the [`TypedMap`] must be implement.
/// Marker may be used to implement multiple key-value type mappings.
pub trait TypedMapKey<Marker = ()>: Eq + Hash {
    /// Type of a value associated with the Key type
    type Value: 'static;
}

const INVALID_KEY: &str = "Broken TypedMap: invalid key type";
const INVALID_VALUE: &str = "Broken TypedMap: invalid value type";

/// A map that can store keys of any type that implements [`TypedMapKey`] and values
/// of type defined by [`TypedMapKey::Value`]. One can use Marker to define multiple
/// "key-value" type mappings. Under the hood the [`std::collections::HashMap`] is used.
///
/// # Examples
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// struct Configs;
/// struct Services;
///
/// #[derive(Hash, PartialEq, Eq)]
/// struct ServiceA(usize);
///
/// // Implement key-value mapping for Configs marker
/// impl TypedMapKey<Configs> for ServiceA {
///     type Value = usize;
/// }
///
/// // Implement key-value mapping for Services marker
/// impl TypedMapKey<Services> for ServiceA {
///     type Value = &'static str;
/// }
///
/// #[derive(Hash, PartialEq, Eq)]
/// struct ServiceB(&'static str);
///
/// // Implement key-value mapping for Configs marker
/// impl TypedMapKey<Configs> for ServiceB {
///     type Value = Vec<&'static str>;
/// }
///
/// // Implement key-value mapping for Services marker
/// impl TypedMapKey<Services> for ServiceB {
///     type Value = usize;
/// }
///
/// // Implement key-value mapping for default (i.e. ()) marker
/// impl TypedMapKey for ServiceB {
///     type Value = String;
/// }
///
/// let mut configs: TypedMap<Configs> = TypedMap::new();
/// let mut services: TypedMap<Services> = TypedMap::new();
/// let mut default: TypedMap = TypedMap::new();
///
/// configs.insert(ServiceA(0), 1);
/// services.insert(ServiceA(0), "one");
/// // Line below would not compile, because TypeMapKey<Marker=()>
/// // is not implemented for Key.
/// // default.insert(Key(0), 1);
///
/// // Line below would not compile, because SerivceA key defines
/// // type value as usize for Configs marker (not &'static str)
/// // configs.insert(ServiceA(0), "one");
///
/// configs.insert(ServiceB("zero"), vec!["one"]);
/// services.insert(ServiceB("zero"), 32);
/// default.insert(ServiceB("zero"), "one".to_owned());
///
/// assert_eq!(configs[&ServiceB("zero")], vec!["one"]);
/// assert_eq!(services[&ServiceB("zero")], 32);
/// assert_eq!(default[&ServiceB("zero")], "one".to_owned());
///
/// ```
pub struct TypedMap<Marker = (), S = RandomState> {
    state: HashMap<TypedKey, TypedMapValue, S>,
    _phantom: PhantomData<Marker>,
}

impl<Marker> TypedMap<Marker> {
    /// Creates a new TypedMap with specified marker type.
    ///
    /// # Examples:
    /// ```rust
    /// use typedmap::TypedMap;
    ///
    /// struct Configs;
    /// let map = TypedMap::<Configs>::new();
    /// ```
    pub fn new() -> Self {
        TypedMap {
            state: Default::default(),
            _phantom: PhantomData,
        }
    }

    /// Creates a new TypedMap with a specified capacity and specified marker type
    pub fn with_capacity(capacity: usize) -> Self {
        TypedMap {
            state: HashMap::with_capacity(capacity),
            _phantom: PhantomData,
        }
    }
}

impl<Marker, S> TypedMap<Marker, S>
where
    S: BuildHasher,
{
    /// Creates a new TypedMap with specified capacity, hasher and marker type.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        TypedMap {
            state: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            _phantom: PhantomData,
        }
    }

    /// Creates a new TypedMap with specified hasher and marker type.
    pub fn with_hasher(hash_builder: S) -> Self {
        TypedMap {
            state: HashMap::with_hasher(hash_builder),
            _phantom: PhantomData,
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, None is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map[&Key(3)], 4);
    /// ```
    pub fn insert<K: 'static + TypedMapKey<Marker>>(
        &mut self,
        key: K,
        value: K::Value,
    ) -> Option<K::Value> {
        let typed_key = TypedKey::from_key(key);
        let value = TypedMapValue::from_value(value);
        let old_value = self.state.insert(typed_key, value);
        old_value.and_then(|v| v.downcast::<K::Value>().ok())
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.get(&Key(3)), Some(&4));
    /// assert_eq!(map.get(&Key(4)), None);
    /// ```
    pub fn get<K: 'static + TypedMapKey<Marker>>(&self, key: &K) -> Option<&K::Value> {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.get(&typed_key as &dyn Key)?;
        Some(value.downcast_ref::<K::Value>().expect(INVALID_VALUE))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    ///
    /// let key = Key(3);
    /// if let Some(value) = map.get_mut(&key) {
    ///     *value += 1;
    /// }
    /// assert_eq!(map.get(&key), Some(&5));
    /// ```
    pub fn get_mut<K: 'static + TypedMapKey<Marker>>(&mut self, key: &K) -> Option<&mut K::Value> {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.get_mut(&typed_key as &dyn Key)?;
        Some(value.downcast_mut::<K::Value>().expect(INVALID_VALUE))
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.get_key_value(&Key(3)), Some((&Key(3), &4)));
    /// assert_eq!(map.get(&Key(4)), None);
    /// ```
    pub fn get_key_value<K: 'static + TypedMapKey<Marker>>(
        &self,
        key: &K,
    ) -> Option<(&K, &K::Value)> {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let (key, value) = self.state.get_key_value(&typed_key as &dyn Key)?;

        Some((
            key.downcast_ref().expect(INVALID_KEY),
            value.downcast_ref().expect(INVALID_VALUE),
        ))
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.remove(&Key(3)), Some(4));
    /// assert_eq!(map.get(&Key(3)), None);
    /// ```
    pub fn remove<K: 'static + TypedMapKey<Marker>>(&mut self, key: &K) -> Option<K::Value> {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.remove(&typed_key as &dyn Key)?;
        Some(value.downcast::<K::Value>().ok().expect(INVALID_VALUE))
    }

    /// Removes a key from the map, returning the stored key and value if the key was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.remove_entry(&Key(3)), Some((Key(3), 4)));
    /// assert_eq!(map.remove(&Key(3)), None);
    /// ```
    pub fn remove_entry<K: 'static + TypedMapKey<Marker>>(
        &mut self,
        key: &K,
    ) -> Option<(K, K::Value)> {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.remove_entry(&typed_key as &dyn Key);
        value.map(|(k, v)| {
            let k = k.downcast::<K>().ok().expect(INVALID_KEY);
            let v = v.downcast::<K::Value>().ok().expect(INVALID_VALUE);
            (k, v)
        })
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(char);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut letters: TypedMap = TypedMap::new();
    /// for ch in "a short treatise on fungi".chars() {
    ///    let counter = letters.entry(Key(ch)).or_insert(0);
    ///    *counter += 1;
    /// }
    /// assert_eq!(letters.get(&Key('s')), Some(&2));
    /// assert_eq!(letters.get(&Key('t')), Some(&3));
    /// assert_eq!(letters.get(&Key('u')), Some(&1));
    /// assert_eq!(letters.get(&Key('y')), None);
    /// ```
    pub fn entry<K: 'static + TypedMapKey<Marker>>(
        &mut self,
        key: K,
    ) -> entry::Entry<'_, K, Marker> {
        let typed_key = TypedKey::from_key(key);
        entry::map_entry(self.state.entry(typed_key))
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// map.insert(Key(3), 4);
    /// assert!(map.contains_key(&Key(3)));
    /// assert!(!map.contains_key(&Key(4)));
    /// ```
    pub fn contains_key<K: 'static + TypedMapKey<Marker>>(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.state.len()
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    ///
    /// let map: TypedMap = TypedMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.state.capacity()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = f32;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(10);
    /// assert!(map.is_empty());
    /// map.insert(Key(3), 4.0);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory for reuse.
    ///
    /// # Examples:
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = f32;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 4.0);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.state.clear();
    }

    /// Reserves capacity for at least additional more elements to be inserted in the HashMap. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows `usize`
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.reserve(1000);
    /// assert!(map.capacity() >= 1000);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.state.reserve(additional)
    }

    /// Shrinks the capacity of the underlying hash map as much as possible.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    ///
    /// let mut map: TypedMap = TypedMap::with_capacity(1000);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() <= 16);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.state.shrink_to_fit();
    }

    /// Returns a reference to the map's BuildHasher.
    pub fn hasher(&self) -> &S {
        self.state.hasher()
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `&'a dyn Any`.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for key in map.keys() {
    ///     let mut found = false;
    ///     if let Some(Key(number)) = key.downcast_ref::<Key>() {
    ///         assert_eq!(*number, 3);
    ///         found = true;
    ///     }
    ///     if let Some(SKey(a_str)) = key.downcast_ref::<SKey>() {
    ///         assert_eq!(*a_str, "four");
    ///         found = true;
    ///     }
    ///     assert!(found);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_> {
        Keys(self.state.keys())
    }

    /// An iterator visiting all values in arbitrary order. The iterator element type is &'a dyn Any.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for value in map.values() {
    ///     let mut found = false;
    ///     if let Some(number) = value.downcast_ref::<u32>() {
    ///         assert_eq!(*number, 3);
    ///         found = true;
    ///     }
    ///     if let Some(number) = value.downcast_ref::<usize>() {
    ///         assert_eq!(*number, 4);
    ///         found = true;
    ///     }
    ///     assert!(found);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_> {
        Values(self.state.values())
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator element type is &'a mut dyn Any.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for value in map.values_mut() {
    ///     let mut found = false;
    ///     if let Some(number) = value.downcast_mut::<u32>() {
    ///         *number += 1;
    ///         found = true;
    ///     }
    ///     if let Some(number) = value.downcast_mut::<usize>() {
    ///         *number += 2;
    ///         found = true;
    ///     }
    ///     assert!(found);
    /// }
    ///
    /// assert_eq!(map[&Key(3)], 4);
    /// assert_eq!(map[&SKey("four")], 6);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_> {
        ValuesMut(self.state.values_mut())
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for key_value in map.drain() {
    ///     match key_value.downcast_pair::<Key>() {
    ///         Ok((key, value)) => {
    ///             assert_eq!(key, Key(3));
    ///             assert_eq!(value, 3u32);
    ///         }
    ///         Err(key_value) => {
    ///             let (key, value) = key_value.downcast_pair::<SKey>().unwrap();
    ///             assert_eq!(key, SKey("four"));
    ///             assert_eq!(value, 4usize);
    ///         }
    ///     }
    /// }
    /// ```
    pub fn drain(&mut self) -> Drain<'_, Marker> {
        Drain(self.state.drain(), PhantomData)
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for key_value in map.iter() {
    ///     if let Some((key, value)) = key_value.downcast_pair_ref::<Key>() {
    ///         assert_eq!(key, &Key(3));
    ///         assert_eq!(value, &3u32);
    ///     }
    ///
    ///     if let Some((key, value)) = key_value.downcast_pair_ref::<SKey>() {
    ///         assert_eq!(key, &SKey("four"));
    ///         assert_eq!(value, &4);
    ///     }
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, Marker> {
        Iter(self.state.iter(), PhantomData)
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the values.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// for mut key_value in map.iter_mut() {
    ///     if let Some((key, value)) = key_value.downcast_pair_mut::<Key>() {
    ///         assert_eq!(key, &Key(3));
    ///         *value += 1;
    ///         assert_eq!(value, &4u32);
    ///     }
    ///     if let Some((key, value)) = key_value.downcast_pair_mut::<SKey>() {
    ///         assert_eq!(key, &SKey("four"));
    ///         *value += 1;
    ///         assert_eq!(value, &5);
    ///     }
    /// }
    ///
    /// assert_eq!(map[&Key(3)], 4);
    /// assert_eq!(map[&SKey("four")], 5);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, Marker> {
        IterMut(self.state.iter_mut(), PhantomData)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(Key(4), 4);
    /// map.insert(Key(5), 5);
    ///
    /// map.retain(|mut kv| *kv.downcast_value::<u32>().unwrap_or(&mut 0) % 2 == 1);
    ///
    /// assert_eq!(map.len(), 2);
    /// assert!(map.contains_key(&Key(5)));
    /// assert!(!map.contains_key(&Key(4)));
    ///
    /// map.retain(|mut kv| kv.downcast_key_ref::<Key>().unwrap().0 <= 3);
    /// assert!(map.contains_key(&Key(3)));
    /// assert!(!map.contains_key(&Key(5)));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(TypedKeyValueMutRef<'_, Marker>) -> bool,
    {
        let g = move |key: &TypedKey, value: &mut TypedMapValue| {
            f(TypedKeyValueMutRef {
                key,
                value,
                _marker: PhantomData,
            })
        };
        self.state.retain(g)
    }
}

impl<Marker> Default for TypedMap<Marker> {
    fn default() -> Self {
        TypedMap::new()
    }
}

impl<Marker> IntoIterator for TypedMap<Marker> {
    type IntoIter = IntoIter<Marker>;
    type Item = TypedKeyValue<Marker>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.state.into_iter(), PhantomData)
    }
}

impl<Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher> Index<&K> for TypedMap<Marker, S> {
    type Output = K::Value;

    fn index(&self, key: &K) -> &K::Value {
        self.get(key).expect("no entry found for key")
    }
}

/// An iterator over the entries of a TypedMap
///
/// This `struct` is created by ['iter'] method on ['TypedMap']. See its documentation for more.
///
/// ['iter']: TypedMap::iter
///
/// # Example
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.iter();
///
#[derive(Clone)]
pub struct Iter<'a, Marker>(
    std::collections::hash_map::Iter<'a, TypedKey, TypedMapValue>,
    PhantomData<Marker>,
);

impl<'a, Marker> Iterator for Iter<'a, Marker> {
    type Item = TypedKeyValueRef<'a, Marker>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some(TypedKeyValueRef {
            key,
            value,
            _marker: PhantomData,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<Marker> ExactSizeIterator for Iter<'_, Marker> {}
impl<Marker> FusedIterator for Iter<'_, Marker> {}

/// A mutable iterator over the entries of a TypedMap
///
/// This `struct` is created by ['iter_mut'] method on ['TypedMap']. See its documentation for more.
///
/// ['iter_mut']: TypedMap::iter_mut
///
/// # Example
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.iter_mut();
/// ```
pub struct IterMut<'a, Marker>(
    std::collections::hash_map::IterMut<'a, TypedKey, TypedMapValue>,
    PhantomData<Marker>,
);

impl<'a, Marker> Iterator for IterMut<'a, Marker> {
    type Item = TypedKeyValueMutRef<'a, Marker>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some(TypedKeyValueMutRef {
            key,
            value,
            _marker: PhantomData,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<Marker> ExactSizeIterator for IterMut<'_, Marker> {}
impl<Marker> FusedIterator for IterMut<'_, Marker> {}

/// An draining iterator over the entries of a `TypedMap`.
///
/// This `struct` is created by the [`drain`] method on [`TypedMap`].
/// See its documentation for more.
///
/// [`drain`]: TypedMap::drain
///
/// # Example
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.into_iter();
/// ```
pub struct Drain<'a, Marker>(
    std::collections::hash_map::Drain<'a, TypedKey, TypedMapValue>,
    PhantomData<Marker>,
);

impl<'a, Marker> Iterator for Drain<'a, Marker> {
    type Item = TypedKeyValue<Marker>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some(TypedKeyValue {
            key,
            value,
            _marker: PhantomData,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<Marker> ExactSizeIterator for Drain<'_, Marker> {}
impl<Marker> FusedIterator for Drain<'_, Marker> {}

/// An owning iterator over the entries of a `TypedMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`TypedMap`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
///
/// # Example
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// ```
pub struct IntoIter<Marker>(
    std::collections::hash_map::IntoIter<TypedKey, TypedMapValue>,
    PhantomData<Marker>,
);

impl<Marker> Iterator for IntoIter<Marker> {
    type Item = TypedKeyValue<Marker>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.0.next()?;
        Some(TypedKeyValue {
            key,
            value,
            _marker: PhantomData,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<Marker> ExactSizeIterator for IntoIter<Marker> {}
impl<Marker> FusedIterator for IntoIter<Marker> {}

/// An iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`keys`] method on [`TypedMap`]. See its
/// documentation for more.
///
/// [`keys`]: TypedMap::keys
///
/// # Example
///
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.keys();
/// ```
#[derive(Clone)]
pub struct Keys<'a>(std::collections::hash_map::Keys<'a, TypedKey, TypedMapValue>);

impl<'a> Iterator for Keys<'a> {
    type Item = &'a dyn Any;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.0.next()?;
        Some(key.as_any())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for Keys<'_> {}
impl FusedIterator for Keys<'_> {}

/// An iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values`] method on [`TypedMap`]. See its
/// documentation for more.
///
/// [`values`]: TypedMap::values
///
/// # Example
///
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.values();
/// ```
#[derive(Clone)]
pub struct Values<'a>(std::collections::hash_map::Values<'a, TypedKey, TypedMapValue>);

impl<'a> Iterator for Values<'a> {
    type Item = &'a dyn Any;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.0.next()?;
        Some(value.as_any())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for Values<'_> {}
impl FusedIterator for Values<'_> {}

/// An mutable iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values`] method on [`TypedMap`]. See its
/// documentation for more.
///
/// [`values`]: TypedMap::values
///
/// # Example
///
/// ```
/// use typedmap::TypedMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedMap = TypedMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.values();
/// ```
pub struct ValuesMut<'a>(std::collections::hash_map::ValuesMut<'a, TypedKey, TypedMapValue>);

impl<'a> Iterator for ValuesMut<'a> {
    type Item = &'a mut dyn Any;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.0.next()?;
        Some(value.as_mut_any())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for ValuesMut<'_> {}
impl FusedIterator for ValuesMut<'_> {}

/// Represents owned pair of key and value.
pub struct TypedKeyValue<Marker> {
    key: TypedKey,
    value: TypedMapValue,
    _marker: PhantomData<Marker>,
}

impl<Marker> TypedKeyValue<Marker> {
    /// Downcast key to reference of `K`. Returns `None` if not possible.
    pub fn downcast_key_ref<K: 'static + TypedMapKey<Marker>>(&self) -> Option<&K> {
        self.key.downcast_ref()
    }

    /// Downcast key to the owned value of type `K`. Returns Err(Self) if not possible.
    pub fn downcast_key<K: 'static + TypedMapKey<Marker>>(self) -> Result<K, Self> {
        let Self {
            key,
            value,
            _marker,
        } = self;
        key.downcast().map_err(|key| Self {
            key,
            value,
            _marker,
        })
    }

    /// Downcast key to reference of `V`. Returns `None` if not possible.
    pub fn downcast_value_ref<V: Any>(&self) -> Option<&V> {
        self.value.downcast_ref()
    }

    /// Downcast key to the owned value of type `V`. Returns Err(Self) if not possible.
    pub fn downcast_value<V: Any>(self) -> Result<V, Self> {
        let Self {
            key,
            value,
            _marker,
        } = self;
        value.downcast().map_err(|value| Self {
            key,
            value,
            _marker,
        })
    }

    /// Downcast key to reference of `K` and value to reference of `K::Value`.
    /// Returns `None` if not possible.
    pub fn downcast_pair_ref<K: 'static + TypedMapKey<Marker>>(&self) -> Option<(&K, &K::Value)> {
        let key = self.downcast_key_ref()?;
        let value = self.downcast_value_ref()?;
        Some((key, value))
    }

    /// Downcast key to owned value of type `K` and value to owned value of type `K::Value`.
    /// Returns Err(Self) if not possible.
    pub fn downcast_pair<K: 'static + TypedMapKey<Marker>>(self) -> Result<(K, K::Value), Self> {
        let Self {
            key,
            value,
            _marker,
        } = self;
        match key.downcast() {
            Ok(key) => match value.downcast() {
                Ok(value) => Ok((key, value)),
                Err(dyn_value) => Err(Self {
                    key: TypedKey::from_key(key),
                    value: dyn_value,
                    _marker,
                }),
            },
            Err(dyn_key) => Err(Self {
                key: dyn_key,
                value,
                _marker,
            }),
        }
    }
}

impl<M> Debug for TypedKeyValue<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TypedKeyValue")
    }
}

/// Represents borrowed pair of key and value.
pub struct TypedKeyValueRef<'a, Marker> {
    key: &'a TypedKey,
    value: &'a TypedMapValue,
    _marker: PhantomData<Marker>,
}

// TODO: Consider whether should use _ref suffix in those methods
impl<'a, Marker> TypedKeyValueRef<'a, Marker> {
    /// Downcast key to reference of `K`. Returns `None` if not possible.
    pub fn downcast_key_ref<K: 'static + TypedMapKey<Marker>>(&self) -> Option<&'a K> {
        self.key.downcast_ref()
    }

    /// Downcast value and returns reference or `None` if downcast failed.
    pub fn downcast_value_ref<V: 'static + Any>(&self) -> Option<&'a V> {
        self.value.downcast_ref()
    }

    /// Downcast key to reference of `K` and value to reference of `K::Value`.
    /// Returns `None` if not possible.
    pub fn downcast_pair_ref<K: 'static + TypedMapKey<Marker>>(
        &self,
    ) -> Option<(&'a K, &'a K::Value)> {
        self.downcast_key_ref()
            .and_then(move |key| self.downcast_value_ref().map(move |value| (key, value)))
    }
}

impl<M> Debug for TypedKeyValueRef<'_, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TypedKeyValueRef")
    }
}

/// Represents mutably borrowed pair of key and value.
pub struct TypedKeyValueMutRef<'a, Marker> {
    key: &'a TypedKey,
    value: &'a mut TypedMapValue,
    _marker: PhantomData<Marker>,
}

impl<'a, Marker> TypedKeyValueMutRef<'a, Marker> {
    /// Downcast key to reference of `K`. Returns `None` if not possible.
    pub fn downcast_key_ref<K: 'static + TypedMapKey<Marker>>(&self) -> Option<&'a K> {
        self.key.downcast_ref()
    }

    /// Downcast value to type `V`. Returns `None` if not possible.
    ///
    /// Note: this function borrows mutably self, and returns mutable reference with lifetime
    /// bounded by that borrow. If you need to obtain mutable reference with hashmap bounded
    /// lifetime ('a), then use `downcast_value` function.
    pub fn downcast_value_mut<'b, V: 'static + Any>(&'b mut self) -> Option<&'b mut V>
    where
        'a: 'b,
    {
        self.value.downcast_mut()
    }

    /// Tries to cast value to mutable reference of V consuming self. This allows to return
    /// mutable reference with 'a lifetime which may be useful when collecting mutable references.
    ///
    /// # Examples:
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// let v: Vec<&mut u32> = map
    ///     .iter_mut()
    ///     .flat_map(|kv| kv.downcast_value::<u32>().ok())
    ///     .collect();
    /// assert_eq!(*v[0], 3);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn downcast_value<V: 'static + Any>(self) -> Result<&'a mut V, Self> {
        if self.value.is::<V>() {
            Ok(self.value.downcast_mut().expect("Unreachable!"))
        } else {
            Err(self)
        }
    }

    /// Downcast key to type `K` and value to type `K::Value`. Returns `None` if not possible.
    ///
    /// Note: this function borrows mutably self, and returns mutable reference with lifetime
    /// bounded by that borrow. If you need to obtain mutable reference with hashmap bounded
    /// lifetime ('a), then use `downcast_pair` function.
    pub fn downcast_pair_mut<'b, K: 'static + TypedMapKey<Marker>>(
        &'b mut self,
    ) -> Option<(&'b K, &'b mut K::Value)>
    where
        'a: 'b,
    {
        self.downcast_key_ref()
            .and_then(move |key| self.downcast_value_mut().map(move |value| (key, value)))
    }

    /// Tries to cast self to key K and value K::Value consuming self.
    /// This allows to return references with 'a lifetime which may be
    /// useful when collecting references to Vec.
    ///
    /// # Examples:
    /// ```
    /// use typedmap::TypedMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct SKey(&'static str);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = u32;
    /// }
    ///
    /// impl TypedMapKey for SKey {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedMap = TypedMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// let v: Vec<(&Key, &mut u32)> = map
    ///     .iter_mut()
    ///     .flat_map(|kv| kv.downcast_pair::<Key>().ok())
    ///     .collect();
    /// assert_eq!(*v[0].0, Key(3));
    /// assert_eq!(*v[0].1, 3);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn downcast_pair<K: 'static + TypedMapKey<Marker>>(
        self,
    ) -> Result<(&'a K, &'a mut K::Value), Self> {
        let key = self.downcast_key_ref();

        let key = match key {
            Some(key) => key,
            None => return Err(self),
        };

        match self.downcast_value() {
            Ok(value) => Ok((key, value)),
            Err(err) => Err(err),
        }
    }
}

impl<M> Debug for TypedKeyValueMutRef<'_, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TypedMutRef")
    }
}

#[cfg(test)]
mod tests {
    use crate::TypedMap;
    use crate::TypedMapKey;
    use std::hash::Hash;

    #[test]
    fn test_basic_use() {
        // FIXME: split test into smaller tests testing one thing at a time
        struct OtherState;

        let mut state = TypedMap::new();
        let mut other_state = TypedMap::<OtherState>::new();

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct AThing;

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct BThing(usize);

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct CThing(usize);

        impl TypedMapKey for AThing {
            type Value = String;
        }

        impl TypedMapKey for BThing {
            type Value = usize;
        }

        impl TypedMapKey<OtherState> for CThing {
            type Value = usize;
        }

        state.insert(AThing, "Example".to_owned());
        state.insert(BThing(32), 33);
        state.insert(BThing(33), 34);
        // This does not compile, as marker is not correct!
        // state.insert(&CThing(0), 33);
        // And this works fine!
        other_state.insert(CThing(0), 33);

        assert_eq!(state.get(&AThing), Some(&"Example".to_owned()));
        assert_eq!(state.get(&BThing(0)), None);
        assert_eq!(state.get(&BThing(32)), Some(&33));
        assert_eq!(state.get(&BThing(33)), Some(&34));
        assert_eq!(other_state.get(&CThing(0)), Some(&33));

        *state.entry(BThing(3)).or_default() += 1;
        assert_eq!(*state.get(&BThing(3)).unwrap(), 1usize);

        *state.entry(BThing(4)).or_insert(3usize) += 1;
        *state.entry(BThing(4)).or_insert(3usize) += 1;
        assert_eq!(*state.get(&BThing(4)).unwrap(), 5usize);

        if let crate::entry::Entry::Occupied(occupied) = state.entry(BThing(3)) {
            let (k, v) = occupied.remove_entry();
            assert_eq!(k, BThing(3));
            assert_eq!(v, 1usize);
        } else {
            panic!()
        }

        let mut b_entries: Vec<_> = state
            .iter()
            .flat_map(|r| r.downcast_pair_ref::<BThing>())
            .collect();
        b_entries.sort_by_key(|kv| (kv.0).0);

        let b4 = BThing(4);
        let b32 = BThing(32);
        let b33 = BThing(33);
        assert_eq!(
            b_entries,
            vec![(&b4, &5usize), (&b32, &33usize), (&b33, &34usize)]
        );

        state.iter_mut().for_each(|mut r| {
            if let Some((_, value)) = r.downcast_pair_mut::<BThing>() {
                *value += 1;
            }
        });

        let b_things: Vec<_> = state
            .iter_mut()
            .flat_map(|r| r.downcast_pair::<BThing>())
            .collect();

        assert_eq!(b_things.len(), 3);
    }

    #[test]
    fn test_always_equal_types() {
        let mut state = TypedMap::default();
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        struct AThing;
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        struct BThing;

        trait Foo {}

        impl Foo for AThing {}
        impl Foo for BThing {}

        impl Hash for Box<dyn Foo> {
            fn hash<H>(&self, hasher: &mut H)
            where
                H: std::hash::Hasher,
            {
                hasher.write_i8(0);
                hasher.finish();
            }
        }

        impl PartialEq for Box<dyn Foo> {
            fn eq(&self, _rhs: &Self) -> bool {
                true
            }
        }

        impl Eq for Box<dyn Foo> {}

        impl TypedMapKey for AThing {
            type Value = String;
        }

        impl TypedMapKey for BThing {
            type Value = usize;
        }

        impl TypedMapKey for Box<dyn Foo> {
            type Value = String;
        }

        let key_a = Box::new(AThing);
        let key_b = Box::new(BThing);

        state.insert(key_a.clone() as Box<dyn Foo>, "test1".to_owned());
        let old_key = state
            .insert(key_b.clone() as Box<dyn Foo>, "test2".to_owned())
            .unwrap();

        assert_eq!(old_key, "test1".to_owned());

        let key_a = &(key_a as Box<dyn Foo>);
        let key_b = &(key_b as Box<dyn Foo>);

        assert_eq!(state.get(key_a).unwrap(), &"test2".to_owned());
        assert_eq!(state.get(key_b).unwrap(), &"test2".to_owned());

        assert_eq!(state.remove(key_a).unwrap(), "test2".to_owned());

        assert!(state.is_empty());
        assert_eq!(state.len(), 0);
    }
}
