# Committable

A hashmap with delta entries that enables quick revert of the recent changes.
Implementation-wise, the hashmap keeps a *delta* map that records the additional
changes on a *base* map. The user can call `DeltaHashMap::commit` to merge the
additional changes into the base map. However, if the user is unsatisfied with
the result of the specific layer of operation, the changes that happens after the
layer can be discarded on demand.

See `DeltaHashMap::commit` and `DeltaHashMap::cocommit` for more information.