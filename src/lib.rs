//! Provides a hash map type that allows to store key-value pair of type any type (K, V) such that
//! K implements [`TypedMapKey`] and [`TypedMapKey::Value`] is V.  
//!
//! ```
//! use typedmap::{TypedMap, TypedMapKey};
//!
//! // Define key types
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct Dog{name: String};
//! #[derive(Debug, PartialEq, Eq, Hash)]
//! struct Cat{name: String};
//!
//! struct Bark{volume: u32};
//! struct Mew{pitch: f32};
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

#[cfg(feature = "dashmap")]
pub mod dashmap;
pub mod hashmap;

#[cfg(feature = "dashmap")]
pub mod dashentry;
pub mod entry;

mod dynhash;
mod typedkey;
mod typedvalue;

#[cfg(feature = "dashmap")]
pub use crate::dashmap::TypedDashMap;
pub use crate::hashmap::{TypedMap, TypedMapKey};
