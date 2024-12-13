# 0.1.0 (March 30, 2021)

- Initial release.

# 0.1.1 

- Fixes in documentation

# 0.2.0 (January 20, 2022)

- Changed signature of TypedDashMap::entry to require &self instead of &mut self ([PR 3](https://github.com/kodieg/typedmap/pull/3)).

# 0.3.0 (June 15, 2022)

- Update version of dash map to 5.3.4

# 0.3.1 (March 12, 2023)

- Fixes bug with downcasting value ref in TypedKeyValue ([PR 8](https://github.com/kodieg/typedmap/pull/8))

# 0.4.0 (May 6, 2023)

- Changes in ([PR 9](https://github.com/kodieg/typedmap/pull/9))
- BREAKING: TypedMap and TypedDashMap take two additional generic types: key bounds & value bounds, that allow to specify additional type constraints onto keys & values (e.g. CloneBounds).
Use AnyBounds or SyncAnyBounds when migrating from 0.3.x version. 
- Added `iter_mut` function for TypedDashMap
- Added macros to easily implement custom bounds struct for your own traits (see bounds module docs)

# 0.5.0 (Apr 2, 2024)

- Changes in ([PR 10](https://github.com/kodieg/typedmap/pull/11))
- Added FromIterator impl for TypedMap and TypedDashMap 
- Added Debug impl for TypedMap and TypedDashMap 
- Added `insert_key_value` functions for TypedMap and TypedDashMap
- Added Clone impl for TypedMap and TypedDashMap when key and values are cloneable 

# 0.6.0 (Dec 13, 2024)

- Fix clippy warnings ([PR 15](https://github.com/kodieg/typedmap/pull/16))
- Upgrade dashmap dependency from 5.5.3 to 6.1.0 ([PR 16](https://github.com/kodieg/typedmap/pull/16))
