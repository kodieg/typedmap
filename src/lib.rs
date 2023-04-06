//! Provides the [`TypedMap`] type, a hash map that allows to store key-value pair of type any type (K, V) such that
//! K implements [`TypedMapKey`] and [`TypedMapKey::Value`] is V.
//!
//! ```
//! use typedmap::{TypedMap, TypedMapKey};
//!
//! // Define key types
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct Dog { name: String }
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct Cat { name: String }
//!
//! struct Bark { volume: u32 }
//! struct Mew { pitch: f32 }
//!
//! // Define value type for key types
//! impl TypedMapKey for Dog {
//!     type Value = Bark;
//! }
//! impl TypedMapKey for Cat {
//!     type Value = Mew;
//! }
//! // Create a new empty map
//! let mut animal_sounds: TypedMap = TypedMap::new();
//! // Insert data
//! animal_sounds.insert(Dog { name: "Spiky".into() }, Bark { volume: 80 });
//! animal_sounds.insert(Cat { name: "Spot".into()  }, Mew  { pitch: 12000.0 });
//!
//! // Get for Dog key get value of type Bark.
//! let spiky_volume = animal_sounds.get(&Dog { name: "Spiky".into() }).unwrap().volume;
//! assert_eq!(spiky_volume, 80);
//! ```
//!
//! One can have multiple implementation
//! of [`TypedMapKey`] for a given type K by specifying `Marker` parameter.
//! For example, in a web service one may keep endpoint configuration
//! and endpoint serivce in two hashmaps.
//! ```
//! struct Configs;
//! struct Services;
//!
//! use typedmap::{TypedMap, TypedMapKey};
//!
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct EndpointGet(String);
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct EndpointPost(usize);
//!
//! struct EndpointGetConfig(String);
//! struct EndpointPostConfig(usize);
//!
//! struct EndpointGetService {}
//! struct EndpointPostService {}
//!
//! impl TypedMapKey<Configs> for EndpointGet {
//!     type Value = EndpointGetConfig;
//! }
//!
//! impl TypedMapKey<Configs> for EndpointPost {
//!     type Value = EndpointPostConfig;
//! }
//!
//! impl TypedMapKey<Services> for EndpointGet {
//!     type Value = EndpointGetService;
//! }
//!
//! impl TypedMapKey<Services> for EndpointPost {
//!     type Value = EndpointPostService;
//! }
//!
//! let mut configs: TypedMap<Configs> = TypedMap::new();
//! let mut services: TypedMap<Services> = TypedMap::new();
//!
//! configs.insert(EndpointGet("test".to_owned()), EndpointGetConfig("config".to_owned()));
//! configs.insert(EndpointPost(10), EndpointPostConfig(20));
//!
//! services.insert(EndpointGet("test".to_owned()), EndpointGetService {});
//! services.insert(EndpointPost(10), EndpointPostService {});
//! ```
//!
//! If `dashmap` feature is enabled, also a dashmap-backed [`TypedDashMap`] is available which allows to
//! perform hashmap operations concurrently.
//! ```
//! struct Configs;
//! struct Serivces;
//!
//! #[cfg(feature = "dashmap")]
//! use typedmap::{TypedDashMap, TypedMapKey};
//! #[cfg(feature = "dashmap")]
//! let mut configs: TypedDashMap<Configs> = TypedDashMap::new();
//! ```
//!
//! By default
//! [`TypedMap`] accepts keys and values that implement [`std::any::Any`] trait (and of course [`TypedMapKey`] trait),
//! while [`TypedDashMap`] requires that keys and values meet `std::any::Any + Send + Sync` bounds.
//! However, both [`TypedMap`] and [`TypedDashMap`] can be parametrized with two type parameters: key bounds (`KB`) and value bounds (`VB`).
//! This mechanism allows to restrict what kind of keys and values can be stored in the hashmap. This crate provides four kind of bounds:
//!  * [`bounds::AnyBounds`] - represents `Any` bounds (used by default in [`TypedMap`]),
//!  * [`bounds::SyncAnyBounds`] - represents `Any + Sync + Send` bounds (used by default in [`TypedDashMap`]),
//!  * [`clone::CloneBounds`] (if `clone` feature is enabled)  - represents `Clone + Any` bounds - allows to restrict keys/values to clonable types,
//!  * [`clone::SyncCloneBounds`] (if `clone` feature is enabled) - represents `Clone + Any + Send + Sync` bounds.
//!
//! These bounds can be specified in the type signature separately for keys and values, e.g.
#![cfg_attr(feature = "clone", doc = r#"
```rust
use typedmap::{TypedMap, TypedMapKey};
use typedmap::clone::{CloneBounds};
let mut map: TypedMap::<(), CloneBounds, CloneBounds, _> = TypedMap::new_with_bounds();
```
"#)]
//!
//! It is possible to define own bounds using [`bounds::Bounds`] and [`bounds::HasBounds`] traits to add custom restrictions to values.
//! For example, you may want to enforce that each value implements a custom `Component` trait.
//! This can be done with a few lines of code using [`crate::impl_custom_bounds`] and [`crate::impl_dyn_trait_wrapper`] macros.
//! ```rust
//! // Your custom marker (could use also () as well)
//! use typedmap::{impl_custom_bounds, impl_dyn_trait_wrapper, SyncAnyBounds, TypedDashMap, TypedMapKey};
//! struct Components;
//!
//! // Trait that each value should implement
//! trait Component {
//!     fn is_ready(&self) -> bool;
//! }
//!
//! // Bounds
//! struct ComponentSyncBounds;
//!
//! // This defines DynComponent that will be Any + Component, used internally to keep values
//! impl_dyn_trait_wrapper!(DynComponent, Component);
//! // This defines new "bounds" struct, that requires to impl Component and uses
//! // dyn DynComponent + Send + Sync as a value container
//! impl_custom_bounds!(ComponentSyncBounds, DynComponent, Component, +Send+Sync);
//!
//! #[derive(Debug, Clone, Eq, PartialEq, Hash)]
//! struct RepositoryKey(usize);
//! struct Repository(String);
//!
//! impl TypedMapKey<Components> for RepositoryKey {
//!     type Value = Repository;
//! }
//!
//! impl Component for Repository {
//!     fn is_ready(&self) -> bool {
//!         true
//!     }
//! }
//!
//! // Create a new TypedDashMap that uses Components marker, keys may be Any, but value must impl Component
//! let state: TypedDashMap<Components, SyncAnyBounds, ComponentSyncBounds> = TypedDashMap::new_with_bounds();
//! state.insert(RepositoryKey(3), Repository("three".into()));
//!
//! let iter = state.iter().filter(|v| {
//!     // We can obtain reference to DynContainer
//!     let dyn_container = v.value_container_ref();
//!     // and from DynContainer reference to &dyn Container using as_object function
//!     let component = dyn_container.as_object();
//!     component.is_ready()
//! });
//! assert_eq!(iter.count(), 1);
//! ```
//!
//! See [`bounds`] for a full example of implementation of bounds.

extern crate core;

pub use crate::bounds::{AnyBounds, SyncAnyBounds};
#[cfg(feature = "dashmap")]
pub use crate::dashmap::TypedDashMap;
pub use crate::hashmap::{TypedMap, TypedMapKey};

pub mod bounds;

#[cfg(feature = "dashmap")]
pub mod dashmap;
pub mod hashmap;

#[cfg(feature = "dashmap")]
pub mod dashentry;
pub mod entry;

#[cfg(feature = "clone")]
pub mod clone;

mod dynhash;
mod typedkey;
mod typedvalue;
