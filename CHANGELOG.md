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

# 0.4.0 (To be released yet)

- BREAKING: TypedMap and TypedDashMap take two additional generic types: key bounds & value bounds, that allow to specify additional type constraints onto keys & values (e.g. CloneBounds).
Use AnyBounds or SyncAnyBounds when migrating from 0.3.x version. 
- Added iter_mut function for TypedDashMap
- Added macros to easily implement custom bounds struct for your own traits (see bounds module docs)
