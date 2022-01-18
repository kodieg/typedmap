use std::any::Any;
use std::hash::BuildHasher;
use std::marker::PhantomData;
use std::ops::Deref;
use std::{fmt::Debug, ops::DerefMut};

use dashmap::DashMap;

use crate::dashentry;
use crate::typedkey::{Key, SyncTypedKey, TypedKeyRef};
use crate::typedvalue::SyncTypedMapValue;
use crate::TypedMapKey;

use std::collections::hash_map::RandomState;

/// A concurrent hash map that can store keys of any type that implements [`TypedMapKey`] and values of
/// type defined by [`TypedMapKey::Value`]. One can use Marker to define multiple "key-value" type
/// mappings. Under the hood the [`DashMap`] is used. Note: that it will deadlock whenever DashMap will.
///
/// # Examples
/// ```
/// use std::sync::Arc;
/// use typedmap::TypedDashMap;
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
/// let configs: Arc<TypedDashMap<Configs>> = Arc::new(TypedDashMap::new());
/// let services: Arc<TypedDashMap<Services>> = Arc::new(TypedDashMap::new());
/// let default: Arc<TypedDashMap> = Arc::new(TypedDashMap::new());
///
/// let configs1 = Arc::clone(&configs);
/// let services1 = Arc::clone(&services);
/// let t1 = std::thread::spawn(move ||{
///     configs1.insert(ServiceA(0), 1);
///     services1.insert(ServiceA(0), "one");
/// });
/// // Line below would not compile, because TypeMapKey<Marker=()>
/// // is not implemented for Key.
/// // default.insert(Key(0), 1);
///
/// // Line below would not compile, because SerivceA key defines
/// // type value as usize for Configs marker (not &'static str)
/// // configs.insert(ServiceA(0), "one");
///
/// let configs2 = Arc::clone(&configs);
/// let services2 = Arc::clone(&services);
/// let default2 = Arc::clone(&default);
/// let t2 = std::thread::spawn(move || {
///     configs2.insert(ServiceB("zero"), vec!["one"]);
///     services2.insert(ServiceB("zero"), 32);
///     default2.insert(ServiceB("zero"), "one".to_owned());
/// });
///
/// t1.join().unwrap();
/// t2.join().unwrap();
///
/// assert_eq!(*configs.get(&ServiceB("zero")).unwrap(), vec!["one"]);
/// assert_eq!(*services.get(&ServiceB("zero")).unwrap(), 32);
/// assert_eq!(*default.get(&ServiceB("zero")).unwrap(), "one".to_owned());
///
/// ```
pub struct TypedDashMap<Marker = (), S = RandomState> {
    state: DashMap<SyncTypedKey, SyncTypedMapValue, S>,
    _phantom: std::marker::PhantomData<Marker>,
}

const INVALID_KEY: &str = "Broken TypedDashMap: invalid key type";
const INVALID_VALUE: &str = "Broken TypedDashMap: invalid value type";

impl<Marker> TypedDashMap<Marker> {
    /// Creates a new TypedDashMap with specified marker type.
    ///
    /// # Examples:
    /// ```rust
    /// use typedmap::TypedMap;
    ///
    /// struct Configs;
    /// let map = TypedMap::<Configs>::new();
    /// ```
    pub fn new() -> Self {
        TypedDashMap {
            state: Default::default(),
            _phantom: PhantomData,
        }
    }

    /// Creates a new TypedDashMap with a specified capacity and specified marker type
    pub fn with_capacity(capacity: usize) -> Self {
        TypedDashMap {
            state: DashMap::with_capacity(capacity),
            _phantom: PhantomData,
        }
    }
}

impl<Marker, S> TypedDashMap<Marker, S>
where
    S: 'static + BuildHasher + Clone,
{
    /// Creates a new TypedDashMap with specified capacity, hasher and marker type.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        TypedDashMap {
            state: DashMap::with_capacity_and_hasher(capacity, hash_builder),
            _phantom: PhantomData,
        }
    }

    /// Creates a new TypedDashMap with specified hasher and marker type.
    pub fn with_hasher(hash_builder: S) -> Self {
        TypedDashMap {
            state: DashMap::with_hasher(hash_builder),
            _phantom: PhantomData,
        }
    }

    /// Inserts a key and a value into the map.
    ///
    /// If the map did not have this key present, None is returned.
    ///
    /// If the map did have this key present, the value is updated, and old value is returned.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Debug, Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.insert(Key(3), 4).is_none());
    /// assert_eq!(map.insert(Key(3), 5), Some(4));
    /// assert_eq!(*map.get(&Key(3)).unwrap(), 5);
    /// ```
    pub fn insert<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: K,
        value: K::Value,
    ) -> Option<K::Value>
    where
        K::Value: Send + Sync,
    {
        let typed_key = SyncTypedKey::from_key(key);
        let value = SyncTypedMapValue::from_value(value);
        let old_value = self.state.insert(typed_key, value)?;

        Some(old_value.downcast::<K::Value>().expect(INVALID_VALUE))
    }

    /// Get the entry of a key if it exists in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.get(&Key(3)).is_none());
    /// map.insert(Key(3), 4);
    /// assert_eq!(*map.get(&Key(3)).unwrap(), 4);
    /// ```
    pub fn get<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: &K,
    ) -> Option<Ref<'_, Marker, K, S>>
    where
        K::Value: Send + Sync,
    {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.get(&typed_key as &dyn Key)?;
        Some(Ref(
            value,
            std::marker::PhantomData,
            std::marker::PhantomData,
        ))
    }
    /// Get mutable entry of a key if it exists in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.get_mut(&Key(3)).is_none());
    /// map.insert(Key(3), 4);
    /// *map.get_mut(&Key(3)).unwrap() = 5;
    /// assert_eq!(*map.get(&Key(3)).unwrap().value(), 5);
    /// ```
    pub fn get_mut<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: &K,
    ) -> Option<RefMut<'_, Marker, K, S>>
    where
        K::Value: Send + Sync,
    {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let value = self.state.get_mut(&typed_key as &dyn Key)?;
        Some(RefMut(
            value,
            std::marker::PhantomData,
            std::marker::PhantomData,
        ))
    }

    /// Check if the map contains a specific key.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(!map.contains_key(&Key(3)));
    /// map.insert(Key(3), 4);
    /// assert!(map.contains_key(&Key(3)));
    /// ```
    pub fn contains_key<K: 'static + TypedMapKey<Marker> + Send + Sync>(&self, key: &K) -> bool
    where
        K::Value: Send + Sync,
    {
        let typed_key = TypedKeyRef::from_key_ref(key);
        self.state.contains_key(&typed_key as &dyn Key)
    }

    /// Removes an entry from the map.
    ///
    /// Returns both key and value if the key existed and the entry was removed. Otherwise returns None.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Debug, Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.remove(&Key(3)).is_none());
    /// map.insert(Key(3), 4);
    /// assert!(map.contains_key(&Key(3)));
    /// assert_eq!(map.remove(&Key(3)), Some((Key(3), 4)));
    /// assert!(!map.contains_key(&Key(3)));
    /// ```
    pub fn remove<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: &K,
    ) -> Option<(K, K::Value)>
    where
        K::Value: Send + Sync,
    {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let (key, value) = self.state.remove(&typed_key as &dyn Key)?;
        let key = key.downcast().ok().expect(INVALID_KEY);
        let value = value.downcast().expect(INVALID_VALUE);
        Some((key, value))
    }

    /// Removes an entry from the map the provided conditional function returned true.
    ///
    /// Returns both key and value if the key existed and the entry was removed. Otherwise returns None.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Debug, Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.remove(&Key(3)).is_none());
    /// map.insert(Key(3), 4);
    /// assert!(map.contains_key(&Key(3)));
    /// assert_eq!(map.remove_if(&Key(3), |k, v| false), None);
    /// assert!(map.contains_key(&Key(3)));
    /// assert_eq!(map.remove_if(&Key(3), |k, v| true), Some((Key(3), 4)));
    /// assert!(!map.contains_key(&Key(3)));
    /// ```
    pub fn remove_if<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: &K,
        f: impl FnOnce(&K, &K::Value) -> bool,
    ) -> Option<(K, K::Value)>
    where
        K::Value: Send + Sync,
    {
        let typed_key = TypedKeyRef::from_key_ref(key);
        let f = move |typed_key: &SyncTypedKey, typed_value: &SyncTypedMapValue| {
            let k = typed_key.downcast_ref().expect(INVALID_KEY);
            let v = typed_value.downcast_ref().expect(INVALID_VALUE);
            f(k, v)
        };
        let (key, value) = self.state.remove_if(&typed_key as &dyn Key, f)?;
        let key = key.downcast().ok().expect(INVALID_KEY);
        let value = value.downcast().expect(INVALID_VALUE);
        Some((key, value))
    }

    /// Get the amount of entries in the map.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq, Debug)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// map.insert(Key(3), 4);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.state.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = f32;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::with_capacity(10);
    /// assert!(map.is_empty());
    /// map.insert(Key(3), 4.0);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// # Examples:
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(usize);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = f32;
    /// }
    ///
    /// let mut map: TypedDashMap = TypedDashMap::new();
    /// map.insert(Key(3), 4.0);
    /// map.clear();
    /// assert!(map.get(&Key(3)).is_none())
    /// // assert!(map.is_empty()); // for some reason this fails
    /// ```
    pub fn clear(&self) {
        self.state.clear();
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
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
    /// let mut map: TypedDashMap = TypedDashMap::new();
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
    pub fn iter(&self) -> Iter<'_, Marker, S> {
        Iter(self.state.iter(), PhantomData)
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
    /// use typedmap::TypedMapKey;
    ///
    /// #[derive(Hash, PartialEq, Eq)]
    /// struct Key(char);
    ///
    /// impl TypedMapKey for Key {
    ///     type Value = usize;
    /// }
    ///
    /// let mut letters: TypedDashMap = TypedDashMap::new();
    /// for ch in "a short treatise on fungi".chars() {
    ///    let mut counter = letters.entry(Key(ch)).or_insert(0);
    ///    *counter += 1;
    /// }
    /// assert_eq!(letters.get(&Key('s')).unwrap().value(), &2);
    /// assert_eq!(letters.get(&Key('t')).unwrap().value(), &3);
    /// assert_eq!(letters.get(&Key('u')).unwrap().value(), &1);
    /// assert!(letters.get(&Key('y')).is_none());
    /// ```
    pub fn entry<K: 'static + TypedMapKey<Marker> + Send + Sync>(
        &self,
        key: K,
    ) -> dashentry::Entry<'_, K, Marker, S>
    where
        K::Value: Send + Sync,
    {
        let typed_key = SyncTypedKey::from_key(key);
        dashentry::map_entry(self.state.entry(typed_key))
    }

    /// Retain elements that the filter closure returns true for.
    ///
    /// # Examples
    /// ```
    /// use typedmap::TypedDashMap;
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
    /// let mut map: TypedDashMap = TypedDashMap::new();
    /// map.insert(Key(3), 3);
    /// map.insert(SKey("four"), 4);
    ///
    /// map.retain(|kv| kv.downcast_key_ref::<Key>().is_some());
    /// assert!(map.contains_key(&Key(3)));
    /// ```
    pub fn retain(&self, mut predicate: impl FnMut(TypedKeyValueRef<Marker>) -> bool) {
        let ff = move |key: &SyncTypedKey, value: &mut SyncTypedMapValue| {
            let kv = TypedKeyValueRef {
                key,
                value,
                _marker: PhantomData,
            };
            predicate(kv)
        };
        self.state.retain(ff);
    }
}

impl<Marker> Default for TypedDashMap<Marker> {
    fn default() -> Self {
        TypedDashMap::new()
    }
}

/// An iterator over the entries of a TypedDashMap
///
/// This `struct` is created by ['iter'] method on [`TypedDashMap`]. See its documentation for more.
///
/// ['iter']: crate::TypedMap::iter
///
/// # Example
/// ```
/// use typedmap::TypedDashMap;
/// use typedmap::TypedMapKey;
///
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct Key(usize);
///
/// impl TypedMapKey for Key {
///     type Value = u32;
/// }
///
/// let mut map: TypedDashMap = TypedDashMap::new();
/// map.insert(Key(3), 3);
/// let iter = map.iter();
///
pub struct Iter<'a, Marker, S>(
    dashmap::iter::Iter<'a, SyncTypedKey, SyncTypedMapValue, S>,
    PhantomData<Marker>,
);

impl<'a, Marker, S: BuildHasher + Clone> Iterator for Iter<'a, Marker, S> {
    type Item = TypedKeyValueGuard<'a, Marker, S>;

    fn next(&mut self) -> Option<Self::Item> {
        let key_value = self.0.next()?;
        Some(TypedKeyValueGuard {
            key_value,
            _marker: PhantomData,
        })
    }
}

pub struct TypedKeyValueGuard<'a, Marker, S> {
    key_value: dashmap::mapref::multiple::RefMulti<'a, SyncTypedKey, SyncTypedMapValue, S>,
    _marker: PhantomData<Marker>,
}

impl<'a, Marker, S: BuildHasher> TypedKeyValueGuard<'a, Marker, S> {
    /// Downcast key to reference of `K`. Returns `None` if not possible.
    pub fn downcast_key_ref<K: 'static + TypedMapKey<Marker>>(&self) -> Option<&'_ K> {
        self.key_value.key().downcast_ref()
    }

    /// Downcast value and returns reference or `None` if downcast failed.
    pub fn downcast_value_ref<V: 'static + Any>(&self) -> Option<&'_ V> {
        self.key_value.value().downcast_ref()
    }

    /// Downcast key to reference of `K` and value to reference of `K::Value`.
    /// Returns `None` if not possible.
    pub fn downcast_pair_ref<K: 'static + TypedMapKey<Marker>>(
        &self,
    ) -> Option<(&'_ K, &'_ K::Value)> {
        let (key, value) = self.key_value.pair();
        Some((key.downcast_ref()?, value.downcast_ref()?))
    }
}

/// An immutable reference
pub struct Ref<'a, Marker, K: 'static + TypedMapKey<Marker>, S>(
    dashmap::mapref::one::Ref<'a, SyncTypedKey, SyncTypedMapValue, S>,
    std::marker::PhantomData<K>,
    std::marker::PhantomData<Marker>,
);

impl<'a, Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher> Ref<'a, Marker, K, S> {
    pub fn key(&self) -> &K {
        self.0.key().downcast_ref::<K>().expect(INVALID_KEY)
    }

    pub fn value(&self) -> &K::Value {
        self.0
            .value()
            .downcast_ref::<K::Value>()
            .expect(INVALID_VALUE)
    }

    pub fn pair(&self) -> (&K, &K::Value) {
        (self.key(), self.value())
    }
}

impl<'a, Marker, K: TypedMapKey<Marker>, S: BuildHasher> Deref for Ref<'a, Marker, K, S> {
    type Target = K::Value;

    fn deref(&self) -> &K::Value {
        self.value()
    }
}

impl<'a, Marker, K: TypedMapKey<Marker>, S> Debug for Ref<'a, Marker, K, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("Ref")
    }
}

/// A mutable reference
pub struct RefMut<'a, Marker, K: 'static + TypedMapKey<Marker>, S>(
    pub(crate) dashmap::mapref::one::RefMut<'a, SyncTypedKey, SyncTypedMapValue, S>,
    pub(crate) std::marker::PhantomData<K>,
    pub(crate) std::marker::PhantomData<Marker>,
);

impl<'a, Marker, K: 'static + TypedMapKey<Marker>, S: BuildHasher> RefMut<'a, Marker, K, S> {
    pub fn key(&self) -> &K {
        self.0.key().downcast_ref::<K>().expect(INVALID_KEY)
    }

    pub fn value(&self) -> &K::Value {
        self.0
            .value()
            .downcast_ref::<K::Value>()
            .expect(INVALID_VALUE)
    }

    pub fn value_mut(&mut self) -> &mut K::Value {
        self.0
            .value_mut()
            .downcast_mut::<K::Value>()
            .expect(INVALID_VALUE)
    }

    pub fn pair(&self) -> (&K, &K::Value) {
        (self.key(), self.value())
    }

    pub fn pair_mut(&mut self) -> (&K, &K::Value) {
        let (key, value) = self.0.pair_mut();
        let key = key.downcast_ref::<K>().expect(INVALID_KEY);
        let value = value.downcast_mut::<K::Value>().expect(INVALID_VALUE);
        (key, value)
    }
}

impl<'a, Marker, K: TypedMapKey<Marker>, S: BuildHasher> Deref for RefMut<'a, Marker, K, S> {
    type Target = K::Value;

    fn deref(&self) -> &K::Value {
        self.value()
    }
}

impl<'a, Marker, K: TypedMapKey<Marker>, S: BuildHasher> DerefMut for RefMut<'a, Marker, K, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value_mut()
    }
}

impl<'a, Marker, K: TypedMapKey<Marker>, S> Debug for RefMut<'a, Marker, K, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str("RefMut")
    }
}

/// Represents borrowed pair of key and value.
pub struct TypedKeyValueRef<'a, Marker> {
    key: &'a SyncTypedKey,
    value: &'a SyncTypedMapValue,
    _marker: PhantomData<Marker>,
}

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

#[cfg(test)]
mod tests {
    use crate::TypedDashMap;
    use crate::TypedMapKey;
    use std::hash::Hash;
    use std::sync::Arc;

    #[test]
    fn test_threads() {
        let map: Arc<TypedDashMap> = Arc::new(TypedDashMap::new());

        #[derive(Debug, Hash, PartialEq, Eq)]
        struct Key(String);

        impl TypedMapKey for Key {
            type Value = String;
        }

        let map1 = map.clone();
        let th1 = std::thread::spawn(move || {
            map1.insert(Key("k1".to_owned()), "v1".to_owned());
        });

        let map2 = map.clone();
        let th2 = std::thread::spawn(move || {
            map2.insert(Key("k2".to_owned()), "v2".to_owned());
        });

        th1.join().unwrap();
        th2.join().unwrap();

        let k1 = Key("k1".to_owned());
        let k2 = Key("k2".to_owned());

        let r = map.get(&k1).unwrap();
        assert_eq!(r.key(), &k1);
        assert_eq!(r.value(), &"v1".to_owned());

        let r = map.get(&k2).unwrap();
        assert_eq!(r.pair(), (&k2, &"v2".to_owned()));
    }
}
