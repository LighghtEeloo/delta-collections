# Delta Collections

Data structures with delta entries that enables quick revert of the recent
changes. Implementation-wise, the data structures keeps a *delta* structure that
records the additional changes on the *base* structure. Take the `HashMap` for
example, the user can call `DeltaHashMap::commit` to merge the additional
changes into the base map. However, if the user is unsatisfied with the result
of the specific layer of operation, the changes that happens after the layer can
be discarded on demand by calling `DeltaHashMap::revert`.

Currently, only hashmaps are supported. Common operations and iterators on the
data structure are also supported.

See `DeltaHashMap::commit`, `DeltaHashMap::revert` and `DeltaHashMap::cocommit`
for more information.