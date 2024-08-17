use super::*;

pub struct Entry<'a, V> {
    pub(crate) value: &'a mut Option<V>,
}

impl<'a, K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut letters = HashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|counter| *counter += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&'a mut self, key: K) -> Entry<'a, V> {
        let state = self.base.get(&key);
        let value = self.delta.entry(key).or_insert_with(|| state.cloned());
        Entry { value }
    }
}

impl<'a, V> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.value.get_or_insert(default)
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map = HashMap::new();
    /// let value = "hoho";
    ///
    /// map.entry("poneyland").or_insert_with(|| value);
    ///
    /// assert_eq!(map["poneyland"], "hoho");
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        self.value.get_or_insert_with(default)
    }

    // /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    // /// This method allows for generating key-derived values for insertion by providing the default
    // /// function a reference to the key that was moved during the `.entry(key)` method call.
    // ///
    // /// The reference to the moved key is provided so that cloning or copying the key is
    // /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// use delta_collections::DeltaHashMap as HashMap;
    // ///
    // /// let mut map: HashMap<&str, usize> = HashMap::new();
    // ///
    // /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    // ///
    // /// assert_eq!(map["poneyland"], 9);
    // /// ```
    // #[inline]
    // pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
    //     match self {
    //         Occupied(entry) => entry.into_mut(),
    //         Vacant(entry) => {
    //             let value = default(entry.key());
    //             entry.insert(value)
    //         }
    //     }
    // }

    // /// Returns a reference to this entry's key.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// use delta_collections::DeltaHashMap as HashMap;
    // ///
    // /// let mut map: HashMap<&str, u32> = HashMap::new();
    // /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    // /// ```
    // #[inline]
    // pub fn key(&self) -> &K {
    //     match *self {
    //         Occupied(ref entry) => entry.key(),
    //         Vacant(ref entry) => entry.key(),
    //     }
    // }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Some(v) = self.value {
            f(v);
        }
        self
    }

    // /// Sets the value of the entry, and returns an `OccupiedEntry`.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(entry_insert)]
    // /// use delta_collections::DeltaHashMap as HashMap;
    // ///
    // /// let mut map: HashMap<&str, String> = HashMap::new();
    // /// let entry = map.entry("poneyland").insert_entry("hoho".to_string());
    // ///
    // /// assert_eq!(entry.key(), &"poneyland");
    // /// ```
    // #[inline]
    // #[unstable(feature = "entry_insert", issue = "65225")]
    // pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
    //     match self {
    //         Occupied(mut entry) => {
    //             entry.insert(value);
    //             entry
    //         }
    //         Vacant(entry) => entry.insert_entry(value),
    //     }
    // }
}

impl<'a, V: Default> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use delta_collections::DeltaHashMap as HashMap;
    ///
    /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        self.or_insert_with(Default::default)
    }
}
