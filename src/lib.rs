//! Data structures with delta entries that enables quick unstage of the recent
//! changes. Implementation-wise, the data structures keeps a *delta* structure that
//! records the additional changes on the *base* structure. Take the `HashMap` for
//! example, the user can call [`DeltaHashMap::commit`] to merge the additional
//! changes into the base map. However, if the user is unsatisfied with the result
//! of the specific layer of operation, the changes that happens after the layer can
//! be discarded on demand by calling [`DeltaHashMap::unstage`].
//!
//! See [`DeltaHashMap::commit`], [`DeltaHashMap::unstage`] and [`DeltaHashMap::cocommit`]
//! for more information.

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
    hash::Hash,
    ops::Index,
};

#[allow(rustdoc::private_intra_doc_links)]
/// A hashmap with delta entries. A change will eventually be committed from
/// [`delta`] down to [`base`] by calling [`Self::commit`]. If the user is
/// unsatisfied with the result of a specific layer of operation, the changes
/// that happens after the layer can be discarded on demand by calling
/// [`Self::unstage`].
///
/// [`base`]: Self::base
/// [`delta`]: Self::delta
#[derive(Clone)]
pub struct DeltaHashMap<K, V> {
    pub(crate) base: HashMap<K, V>,
    pub(crate) delta: HashMap<K, Option<V>>,
}

/// An (incomplete) entry API implementation.
pub mod entry;
/// Iterator implementations.
pub mod iter;
/// Serialization and deserialization implementations.
#[cfg(feature = "serde")]
mod serde;

impl<K, V> DeltaHashMap<K, V> {
    /// Creates an empty `DeltaHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::new();
    /// ```
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        DeltaHashMap {
            base: HashMap::new(),
            delta: HashMap::new(),
        }
    }

    /// Unstages the operations kept in delta.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::from_iter([
    ///     (1, "a"),
    /// ]);
    /// map.insert(2, "b");
    /// assert_eq!(map.len(), 2);
    ///
    /// map.unstage();
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn unstage(&mut self) {
        self.delta.clear()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut a = HashMap::new();
    /// a.insert(1, "a");
    /// let len_before_clear = a.len();
    /// assert_eq!(a.len(), 1);
    ///
    /// a.clear();
    ///
    /// assert!(a.is_empty());
    /// assert_eq!(a.len(), 0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        self.base.clear();
        self.delta.clear();
    }

    /// Returns reference of internal base map. It's marked unsafe because the
    /// user must not violate the invariants enforced on the field.
    #[inline]
    pub unsafe fn base_ref(&self) -> &HashMap<K, V> {
        &self.base
    }
    /// Returns reference of internal delta map. It's marked unsafe because the
    /// user must not violate the invariants enforced on the field.
    #[inline]
    pub unsafe fn delta_ref(&self) -> &HashMap<K, Option<V>> {
        &self.delta
    }
    /// Returns mutable reference of internal base map. It's marked unsafe
    /// because the user must not violate the invariants enforced on the field.
    #[inline]
    pub unsafe fn base_ref_mut(&mut self) -> &mut HashMap<K, V> {
        &mut self.base
    }
    /// Returns mutable reference of internal delta map. It's marked unsafe
    /// because the user must not violate the invariants enforced on the field.
    #[inline]
    pub unsafe fn delta_ref_mut(&mut self) -> &mut HashMap<K, Option<V>> {
        &mut self.delta
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
{
    /// Insert data to the delta map. Different from [`Self::insert`], this
    /// function is cheaper because it doesn't return the previously-existed
    /// value in the base map, if any; all it does is return the state presented
    /// in the delta map.
    #[inline]
    pub fn insert_delta(&mut self, k: K, v: V) -> Option<V> {
        self.delta.insert(k, Some(v)).flatten()
    }

    /// Get reference of a key in the delta map. See [`Self::get`] for a
    /// behavior similar to [`HashMap`].
    #[inline]
    pub fn get_delta<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.delta.get(k).map(Option::as_ref).flatten()
    }

    /// Get mutable reference of a key in the delta map. See [`Self::get_mut`]
    /// for a behavior similar to [`HashMap`].
    #[inline]
    pub fn get_mut_delta<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.delta.get_mut(k).map(Option::as_mut).flatten()
    }

    /// Get reference of a key value pair in the delta map. See
    /// [`Self::get_key_value`] for a behavior similar to [`HashMap`].
    #[inline]
    pub fn get_key_value_delta<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.delta
            .get_key_value(key)
            .map(|(k, state)| state.as_ref().and_then(|v| Some((k, v))))
            .flatten()
    }

    /// Remove data from the delta map. See [`Self::remove`] for a behavior
    /// similar to [`HashMap`].
    #[inline]
    pub fn remove_delta(&mut self, k: K) -> Option<V> {
        self.delta.insert(k, None).flatten()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let mut cnt = HashSet::new();
        for key in self.base.keys() {
            cnt.insert(key);
        }
        for (key, val) in self.delta.iter() {
            match val {
                Some(_) => cnt.insert(key),
                None => cnt.remove(key),
            };
        }
        cnt.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.delta.get(key) {
            Some(state) => {
                // the entry exists in cache, either:
                // 1. Some, it's inserted or modified
                // 2. None, it's removed
                state.as_ref()
            }
            None => {
                // the entry doesn't exist in cache
                self.base.get(key)
            }
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.delta.get_key_value(key) {
            Some((key, state)) => {
                // the entry exists in cache, either:
                // 1. Some, it's inserted or modified
                // 2. None, it's removed
                state.as_ref().map(|state| (key, state))
            }
            None => {
                // the entry doesn't exist in cache
                self.base.get_key_value(key)
            }
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.delta.get(key) {
            Some(state) => state.is_some(),
            None => self.base.contains_key(key),
        }
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Clone + Hash + Eq,
{
    /// Retains only the elements specified by the predicate. Keeps the
    /// allocated memory for reuse.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(&k, &v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap;
    ///
    /// let mut map: DeltaHashMap<i32, i32> = (0..8).map(|x|(x, x*10)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// map.retain(|&k, _| k % 2 == 0);
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 0), (2, 20), (4, 40), (6, 60)]);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: Fn(&K, &V) -> bool,
    {
        let mut discard = HashSet::new();
        for (key, value) in self.base.iter() {
            if !f(key, value) {
                discard.insert(key.clone());
            }
        }
        for (key, state) in self.delta.iter_mut() {
            match state {
                Some(value) => {
                    if !f(key, value) {
                        discard.remove(key);
                        *state = None
                    }
                }
                None => {}
            }
        }
        for key in discard {
            self.delta.insert(key, None);
        }
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [`std::collections`]
    /// [module-level documentation] for more.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`std::collections`]: https://doc.rust-lang.org/std/collections/index.html
    /// [module-level documentation]: https://doc.rust-lang.org/std/collections/index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let base_old_value = self.base.get(&key);
        match self.delta.insert(key, Some(value)) {
            Some(old) => {
                // since old exists in cache, the cache is modified, and:
                // if old is Some, then it was inserted after the last checkpoint;
                // if old is None, then it was removed after the last checkpoint
                old
            }
            None => {
                // the old doesn't exist, need to query base to actually return the proper old value
                base_old_value.cloned()
            }
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.entry(key).value.as_mut()
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(1), Some("a"));
    /// assert_eq!(map.remove(1), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(&mut self, key: K) -> Option<V> {
        // self.base.remove(k)
        match self.delta.get_mut(&key) {
            Some(state) => std::mem::replace(state, None),
            None => {
                let state = self.base.get(&key);
                self.delta.insert(key, None);
                state.cloned()
            }
        }
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
    #[allow(rustdoc::private_intra_doc_links)]
    /// Commits the cached operations by merging the results to base. This
    /// function mutates [`DeltaHashMap::base`] and is irrevertable.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// map.insert("d", 4);
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("d"), None);
    ///     assert_eq!(map.delta_ref().get("d"), Some(&Some(4)));
    /// }
    ///
    /// map.commit();
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("d"), Some(&4));
    ///     assert_eq!(map.delta_ref().get("d"), None);
    /// }
    ///
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn commit(&mut self) {
        let cache = std::mem::replace(&mut self.delta, HashMap::new());
        for (key, state) in cache.into_iter() {
            match state {
                Some(value) => {
                    self.base.insert(key, value);
                }
                None => {
                    self.base.remove(&key);
                }
            }
        }
    }
}

impl<K, V> From<HashMap<K, V>> for DeltaHashMap<K, V> {
    fn from(base: HashMap<K, V>) -> Self {
        Self {
            base,
            delta: HashMap::new(),
        }
    }
}

impl<K, V> Into<HashMap<K, V>> for DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
    fn into(mut self) -> HashMap<K, V> {
        self.commit();
        self.base
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Clone + Hash + Eq,
    V: Clone,
{
    /// Commits the base map to the cache. It speeds up the lookup of cache in
    /// many cases. This function does not change the result of up-coming
    /// operations on the hash map.
    ///
    /// The function returns a `&mut Option<V>`. To change the value, call
    /// [`Option::as_mut`]. To delete the entry, assign it to [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("c"), Some(&3));
    ///     assert_eq!(map.delta_ref().get("c"), None);
    /// }
    ///
    /// assert_eq!(map.cocommit_key("c"), &mut Some(3));
    /// if let Some(x) = map.cocommit_key("c").as_mut() {
    ///     *x = 6;
    /// }
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("c"), Some(&3));
    ///     assert_eq!(map.delta_ref().get("c"), Some(&Some(6)));
    /// }
    ///
    /// map.commit();
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("c"), Some(&6));
    ///     assert_eq!(map.delta_ref().get("c"), None);
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn cocommit_key(&mut self, key: K) -> &mut Option<V> {
        let base_value = self.base.get(&key);
        self.delta.entry(key).or_insert_with(|| base_value.cloned())
    }

    /// Commits the base map to the cache. It speeds up the lookup of cache in
    /// many cases. This function does not change the result of up-coming
    /// operations on the hash map.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("c"), Some(&3));
    ///     assert_eq!(map.delta_ref().get("c"), None);
    /// }
    ///
    /// map.cocommit();
    /// unsafe {
    ///     assert_eq!(map.base_ref().get("c"), Some(&3));
    ///     assert_eq!(map.delta_ref().get("c"), Some(&Some(3)));
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn cocommit(&mut self) {
        for (key, value) in self.base.iter() {
            self.delta
                .entry(key.clone())
                .or_insert_with(|| Some(value.clone()));
        }
    }
}

impl<K, V> PartialEq for DeltaHashMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    #[inline]
    fn eq(&self, other: &DeltaHashMap<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V> Eq for DeltaHashMap<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K, V> Debug for DeltaHashMap<K, V>
where
    K: Debug + Hash + Eq,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> Default for DeltaHashMap<K, V> {
    /// Creates an empty `HashMap<K, V, S>`, with the `Default` value for the hasher.
    #[inline]
    fn default() -> DeltaHashMap<K, V> {
        DeltaHashMap::new()
    }
}

impl<K, Q: ?Sized, V> Index<&Q> for DeltaHashMap<K, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `HashMap`.
    #[inline]
    fn index(&self, key: &Q) -> &Self::Output {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for DeltaHashMap<K, V>
where
    K: Eq + Hash,
{
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map1 = HashMap::from([(1, 2), (3, 4)]);
    /// let map2: HashMap<_, _> = [(1, 2), (3, 4)].into();
    /// assert_eq!(map1, map2);
    /// ```
    #[inline]
    fn from(arr: [(K, V); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<K, V> Extend<(K, V)> for DeltaHashMap<K, V>
where
    K: Eq + Hash,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.delta
            .extend(iter.into_iter().map(|(k, v)| (k, Some(v))))
    }
}
