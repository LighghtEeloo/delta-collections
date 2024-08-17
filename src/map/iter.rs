use super::*;
use std::iter::{ExactSizeIterator, FusedIterator};

impl<K, V> DeltaHashMap<K, V> {
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
            delta: self.delta.iter(),
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
}

impl<K, V> DeltaHashMap<K, V>
where
    K: Hash + Eq,
    V: Clone,
{
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
    K: Clone + Hash + Eq,
    V: Clone,
{
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
        // Todo: lazy cocommit
        self.cocommit();
        IterMut {
            delta: self.delta.iter_mut(),
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
    delta: std::collections::hash_map::Iter<'a, K, Option<V>>,
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
    delta: std::collections::hash_map::IterMut<'a, K, Option<V>>,
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
        while let Some((key, state)) = self.delta.next() {
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
            match self.delta.next() {
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
