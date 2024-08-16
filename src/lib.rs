//! Data structures with delta entries that enables quick revert of the recent
//! changes. Implementation-wise, the data structures keeps a *delta* structure that
//! records the additional changes on the *base* structure. Take the `HashMap` for
//! example, the user can call [`DeltaHashMap::commit`] to merge the additional
//! changes into the base map. However, if the user is unsatisfied with the result
//! of the specific layer of operation, the changes that happens after the layer can
//! be discarded on demand by calling [`DeltaHashMap::revert`].
//!
//! See [`DeltaHashMap::commit`], [`DeltaHashMap::revert`] and [`DeltaHashMap::cocommit`]
//! for more information.

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
    hash::Hash,
    iter::{ExactSizeIterator, FusedIterator},
    ops::Index,
};

#[allow(rustdoc::private_intra_doc_links)]
/// A hashmap with delta entries. A change will eventually be committed from
/// [`delta`] down to [`base`] by calling [`Self::commit`]. If the user is
/// unsatisfied with the result of a specific layer of operation, the changes
/// that happens after the layer can be discarded on demand by calling
/// [`Self::revert`].
///
/// [`base`]: Self::base
/// [`delta`]: Self::delta
#[derive(Clone)]
pub struct DeltaHashMap<K, V> {
    pub(crate) base: HashMap<K, V>,
    pub(crate) delta: HashMap<K, Option<V>>,
}

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

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            discard: HashSet::new(),
            base: self.base.iter(),
            cache: self.delta.iter(),
        }
    }

    /// Reverts the operations kept in delta.
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
    /// map.revert();
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn revert(&mut self) {
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

    #[inline]
    pub unsafe fn base_ref(&self) -> &HashMap<K, V> {
        &self.base
    }
    #[inline]
    pub unsafe fn delta_ref(&self) -> &HashMap<K, Option<V>> {
        &self.delta
    }
    #[inline]
    pub unsafe fn base_ref_mut(&mut self) -> &mut HashMap<K, V> {
        &mut self.base
    }
    #[inline]
    pub unsafe fn delta_ref_mut(&mut self) -> &mut HashMap<K, Option<V>> {
        &mut self.delta
    }
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
{
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

    #[inline]
    pub fn insert_delta(&mut self, k: K, v: V) {
        self.delta.insert(k, Some(v));
    }
    #[inline]
    pub fn get_delta<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.delta.get(k).map(Option::as_ref).flatten()
    }
    #[inline]
    pub fn get_mut_delta<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.delta.get_mut(k).map(Option::as_mut).flatten()
    }
    #[inline]
    pub fn remove_delta(&mut self, k: K) {
        self.delta.insert(k, None);
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
{
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
    K: Hash + Eq,
    V: Clone,
{
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
        let state = self.base.get(&key);
        self.delta
            .entry(key)
            .or_insert_with(|| state.cloned())
            .as_mut()
    }

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

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<&str> = map.into_keys().collect();
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<i32> = map.into_values().collect();
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            inner: self.into_iter(),
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

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
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
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
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
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.cocommit();
        IterMut {
            base: self.delta.iter_mut(),
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

/// An iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`iter`]: HashMap::iter
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter();
/// ```
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a> {
    discard: HashSet<&'a K>,
    base: std::collections::hash_map::Iter<'a, K, V>,
    cache: std::collections::hash_map::Iter<'a, K, Option<V>>,
}

/// A mutable iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: HashMap::iter_mut
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let mut map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter_mut();
/// ```
#[derive(Debug)]
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: std::collections::hash_map::IterMut<'a, K, Option<V>>,
}

/// An owning iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`HashMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.into_iter();
/// ```
#[derive(Debug)]
pub struct IntoIter<K, V> {
    base: std::collections::hash_map::IntoIter<K, V>,
}

/// An iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`keys`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`keys`]: HashMap::keys
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_keys = map.keys();
/// ```
#[derive(Clone, Debug)]
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

/// An iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`values`]: HashMap::values
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.values();
/// ```
#[derive(Clone, Debug)]
pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

/// A mutable iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: HashMap::values_mut
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let mut map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.values_mut();
/// ```
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: IterMut<'a, K, V>,
}

/// An owning iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`into_keys`]: HashMap::into_keys
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_keys = map.into_keys();
/// ```
#[derive(Debug)]
pub struct IntoKeys<K, V> {
    inner: IntoIter<K, V>,
}

/// An owning iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`into_values`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`into_values`]: HashMap::into_values
///
/// # Example
///
/// ```
/// use delta_collections::DeltaHashMap as HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.into_values();
/// ```
#[derive(Debug)]
pub struct IntoValues<K, V> {
    inner: IntoIter<K, V>,
}

impl<'a, K, V> IntoIterator for &'a DeltaHashMap<K, V>
where
    K: Hash + Eq,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut DeltaHashMap<K, V>
where
    K: Clone + Hash + Eq,
    V: Clone,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    #[inline]
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V> IntoIterator for DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Not possible with .iter()
    /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// ```
    #[inline]
    fn into_iter(mut self) -> IntoIter<K, V> {
        // since the map will no longer be used, we can safely commit
        self.commit();
        // ... and take the base
        IntoIter {
            base: self.base.into_iter(),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Hash + Eq,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        while let Some((key, state)) = self.cache.next() {
            self.discard.insert(key);
            match state {
                Some(value) => return Some((key, value)),
                None => continue,
            }
        }
        // exhausted cache, keep searching in base
        while let Some((key, value)) = self.base.next() {
            if self.discard.contains(key) {
                continue;
            }
            return Some((key, value));
        }
        // exhausted both iterators
        None
    }
}
impl<K, V> FusedIterator for Iter<'_, K, V> where K: Hash + Eq {}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        loop {
            match self.base.next() {
                Some((key, Some(value))) => break Some((key, value)),
                Some((_key, None)) => continue,
                None => break None,
            }
        }
    }
}
impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.base.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.base.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.base.fold(init, f)
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}
impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<'a, K, V> Iterator for Keys<'a, K, V>
where
    K: Hash + Eq,
{
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}
impl<K, V> FusedIterator for Keys<'_, K, V> where K: Hash + Eq {}

impl<'a, K, V> Iterator for Values<'a, K, V>
where
    K: Hash + Eq,
{
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}
impl<K, V> FusedIterator for Values<'_, K, V> where K: Hash + Eq {}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V>
where
    K: Hash + Eq,
{
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}
impl<K, V> FusedIterator for ValuesMut<'_, K, V> where K: Hash + Eq {}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}
impl<K, V> ExactSizeIterator for IntoKeys<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for IntoKeys<K, V> {}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for IntoValues<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for IntoValues<K, V> {}

impl<K, V> FromIterator<(K, V)> for DeltaHashMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> DeltaHashMap<K, V> {
        let mut base = HashMap::new();
        let cache = HashMap::new();
        base.extend(iter);
        DeltaHashMap { base, delta: cache }
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
