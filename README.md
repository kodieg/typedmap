# TypedMap

[![Docs](https://docs.rs/typedmap/badge.svg)](https://docs.rs/crate/typedmap/)
[![Crates.io](https://img.shields.io/crates/v/typedmap.svg)](https://crates.io/crates/typedmap)

`TypedMap` is a typed `HashMap`. It allows you to define different value type depending on a Key type. It's useful if you want to store different key-value pairs in a single hashmap, for example in HTTP app that implements multiple services.


```rust
use typedmap::{TypedMap, TypedMapKey};

// Define key types
#[derive(Debug, PartialEq, Eq, Hash)]
struct Dog{name: String};
#[derive(Debug, PartialEq, Eq, Hash)]
struct Cat{name: String};

struct Bark{volume: u32};
struct Mew{pitch: f32};

// Define value type for key types
impl TypedMapKey for Dog {
    type Value = Bark;
}
impl TypedMapKey for Cat {
    type Value = Mew;
}
// Create a new empty map
let mut animal_sounds: TypedMap = TypedMap::new();
// Insert data
animal_sounds.insert(Dog { name: "Spiky".into() }, Bark { volume: 80 });
animal_sounds.insert(Cat { name: "Spot".into()  }, Mew  { pitch: 12000.0 });

// Get for Dog key get value of type Bark.
let spiky_volume = animal_sounds.get(&Dog { name: "Spiky".into() }).unwrap().volume;
assert_eq!(spiky_volume, 80); 
```

```rust
// Define key types
#[derive(Debug, PartialEq, Eq, Hash)]
struct EndpointGet(String);
#[derive(Debug, PartialEq, Eq, Hash)]
struct EndpointPost(usize);

// Define value type for key types
impl TypedMapKey for EndpointGet {
    type Value = String;
}

impl TypedMapKey for EndpointPost {
    type Value = u32;
}

// Create a new empty map
let mut data: TypedMap = TypedMap::new();

// Insert data
data.insert(EndpointGet("test".to_owned()), "data".to_owned());
data.insert(EndpointPost(32), 32);
```

You can use special `Marker` type to create more "type" key-value bindings.

```rust
struct Configs;
struct Services;

use typedmap::{TypedMap, TypedMapKey};

#[derive(Debug, PartialEq, Eq, Hash)]
struct EndpointGet(String);
#[derive(Debug, PartialEq, Eq, Hash)]
struct EndpointPost(usize);

struct EndpointGetConfig(String);
struct EndpointPostConfig(usize);

struct EndpointGetService {}

impl TypedMapKey<Configs> for EndpointGet {
    type Value = EndpointGetConfig;
}

impl TypedMapKey<Configs> for EndpointPost {
    type Value = EndpointPostConfig;
}

impl TypedMapKey<Services> for EndpointGet {
    type Value = EndpointGetService;
}

impl TypedMapKey<Services> for EndpointPost {
    type Value = EndpointPostService;
}


let mut configs: TypedMap<Configs> = TypedMap::new();
let mut services: TypedMap<Services> = TypedMap::new();

configs.insert(EndpointGet("test".to_owned()), EndpointGetConfig("config".to_owned()));
configs.insert(EndpointPost(10), EndpointPostConfig(20));

services.insert(EndpointGet("test".to_owned()), EndpointGetService {});
services.insert(EndpointPost(10), EndpointPostService {});
```

If `dashmap` feature is enabled, one can use `TypedDashMap` that can be used concurrently, as it's using `Dashmap` under the hood.

```rust
use std::sync::Arc;
use typedmap::TypedDashMap;
use typedmap::TypedMapKey;

struct Configs;
struct Services;

#[derive(Hash, PartialEq, Eq)]
struct ServiceA(usize);

// Implement key-value mapping for Configs marker
impl TypedMapKey<Configs> for ServiceA {
    type Value = usize;
}

// Implement key-value mapping for Services marker
impl TypedMapKey<Services> for ServiceA {
    type Value = &'static str;
}

#[derive(Hash, PartialEq, Eq)]
struct ServiceB(&'static str);

// Implement key-value mapping for Configs marker
impl TypedMapKey<Configs> for ServiceB {
    type Value = Vec<&'static str>;
}

// Implement key-value mapping for Services marker
impl TypedMapKey<Services> for ServiceB {
    type Value = usize;
}

// Implement key-value mapping for default (i.e. ()) marker
impl TypedMapKey for ServiceB {
    type Value = String;
}

let configs: Arc<TypedDashMap<Configs>> = Arc::new(TypedDashMap::new());
let services: Arc<TypedDashMap<Services>> = Arc::new(TypedDashMap::new());
let default: Arc<TypedDashMap> = Arc::new(TypedDashMap::new());

let configs1 = Arc::clone(&configs);
let services1 = Arc::clone(&services);
let t1 = std::thread::spawn(move ||{
    configs1.insert(ServiceA(0), 1);
    services1.insert(ServiceA(0), "one");
});

// Line below would not compile, because TypeMapKey<Marker=()>
// is not implemented for Key.
// default.insert(Key(0), 1);

// Line below would not compile, because SerivceA key defines
// type value as usize for Configs marker (not &'static str)
// configs.insert(ServiceA(0), "one");

let configs2 = Arc::clone(&configs);
let services2 = Arc::clone(&services);
let default2 = Arc::clone(&default);
let t2 = std::thread::spawn(move || {
    configs2.insert(ServiceB("zero"), vec!["one"]);
    services2.insert(ServiceB("zero"), 32);
    default2.insert(ServiceB("zero"), "one".to_owned());
});

t1.join().unwrap();
t2.join().unwrap();
```

## Related:

 * type-map - hashmap that uses types as keys

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
