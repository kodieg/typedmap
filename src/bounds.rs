//! Restricting types that may be stored in the hashmap.
//!
//! Struct that implement [`Bounds`] trait may be used as a restriction on types for keys or values
//! stored in the hashmap. Imagine that you'd like to store only values that implement some trait, e.g.
//! service. One can implement new bounds in the following way:
//! ```rust
//! use std::any::Any;
//! use std::hash::Hash;
//! use typedmap::bounds::{Bounds, ContainerWithHash, HasBounds};
//! use typedmap::{AnyBounds, TypedMap, TypedMapKey};
//!
//! // Your trait that map values must implement
//! trait Service {
//!     fn is_ready(&self) -> bool;
//! }
//!
//! // You need a struct to represent bounds requirement
//! struct ServiceBounds;
//!
//! impl Bounds for ServiceBounds {
//!     // Specify trait object type for keys (use dyn ContainerWithHash<Self> + Marker traits
//!     type KeyContainer = dyn ContainerWithHash<ServiceBounds>;
//!     // Specify trait object type for values (must be castable to Any and to Service trait)
//!     type Container = dyn DynService;
//!
//!     // Implement basic conversion functions
//!     fn as_any(this: &Self::Container) -> &dyn Any {
//!          this.as_any()
//!     }
//!
//!     fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any {
//!         this.as_mut_any()
//!     }
//!
//!     fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any> {
//!         this.as_box_any()
//!     }
//! }
//!
//! // Implement HasBounds trait with simple conversion functions
//! impl<T: DynService> HasBounds<T> for ServiceBounds {
//!     fn cast_box(this: Box<T>) -> Box<Self::Container> {
//!         this
//!     }
//!
//!     fn as_ref(this: &T) -> &Self::Container {
//!         this
//!     }
//!
//!     fn as_mut(this: &mut T) -> &mut Self::Container {
//!         this
//!     }
//!
//!     fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer> where T: 'static + Sized + Hash + Eq {
//!         this
//!     }
//! }
//!
//! // Implement trait object type
//! trait DynService: Any + Service {
//!     fn as_service(&self) -> &dyn Service;
//!
//!     fn as_any(&self) -> &dyn Any;
//!     fn as_mut_any(&mut self) -> &mut dyn Any;
//!     fn as_box_any(self: Box<Self>) -> Box<dyn Any>;
//! }
//!
//! impl<T: Service + Any> DynService for T {
//!     fn as_service(&self) -> &dyn Service {
//!         self
//!     }
//!
//!     fn as_any(&self) -> &dyn Any {
//!         self
//!     }
//!
//!     fn as_mut_any(&mut self) -> &mut dyn Any {
//!         self
//!     }
//!
//!     fn as_box_any(self: Box<Self>) -> Box<dyn Any> {
//!         self
//!     }
//! }
//!
//! #[derive(Eq, PartialEq, Hash)]
//! struct Key;
//!
//! impl TypedMapKey for Key {
//!     type Value = ServiceA;
//! }
//!
//! struct ServiceA;
//! impl Service for ServiceA {
//!     fn is_ready(&self) -> bool {
//!         true
//!     }
//! }
//!
//! // Use it
//! let mut map: TypedMap<(), AnyBounds, ServiceBounds, _> = TypedMap::new_with_bounds();
//! map.insert(Key, ServiceA);
//!
//! for kv in map.iter() {
//!    // use function from Service trait;
//!    let _ = kv.value_container_ref().as_service().is_ready();
//! }
//!
//! ```
use std::any::Any;
use std::hash::Hash;

use crate::dynhash::DynHash;

/// Represents bounds for key or values. This allows to enforce TypedMap to store for example
/// only cloneable values or ones that are Send+Sync.
pub trait Bounds
where
    Self: Sized,
{
    /// Type used to store keys with those bounds. It should be `dyn ContainerWithHash<Self> + Marker traits`
    ///
    /// In most cases `dyn ContainerWithHash<Self>` or `dyn ContainerWithHash<Self> + Send + Sync` are good options.
    type KeyContainer: ?Sized + ContainerWithHash<Self>;
    /// Type used to store values that fulfill specified bounds (e.g. `dyn Any + Send + Sync` or
    /// `dyn CloneAny`)
    type Container: ?Sized;

    // Conversions from Container type to Any
    fn as_any(this: &Self::Container) -> &dyn Any;
    fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any;
    fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any>;
}

/// Trait that marks that specific type fulfill specified bounds.
/// For example `HasBounds<CloneBounds>` is implemented for all types that are implement Clone & Any.
pub trait HasBounds<T: 'static>: Bounds {
    // Conversions from self to Container type
    fn cast_box(this: Box<T>) -> Box<Self::Container>;
    fn as_ref(this: &T) -> &Self::Container;
    fn as_mut(this: &mut T) -> &mut Self::Container;

    // Conversion from self to KeyContainer type
    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq;

    fn box_key(this: T) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        Self::cast_key_box(Box::new(this))
    }

    fn box_value(this: T) -> Box<Self::Container>
    where
        Self: Sized,
    {
        Self::cast_box(Box::new(this))
    }

    fn downcast_ref(this: &Self::Container) -> Option<&T>
    where
        Self: 'static + Sized,
    {
        let any = Self::as_any(this);
        any.downcast_ref()
    }
    fn downcast_mut(this: &mut Self::Container) -> Option<&mut T>
    where
        Self: 'static + Sized,
    {
        let any = Self::as_any_mut(this);
        any.downcast_mut()
    }
    fn downcast_box(this: Box<Self::Container>) -> Result<Box<T>, Box<Self::Container>>
    where
        Self: 'static + Sized,
    {
        if Self::as_any(&this).is::<T>() {
            let any = Self::as_any_box(this);
            Ok(any
                .downcast()
                .unwrap_or_else(|_| panic!("could not downcast!")))
        } else {
            Err(this)
        }
    }
}

/// Trait used as container for keys, i.e. instances of types that meet bounds `B` and implement Hash & Eq
/// Use `dyn ContainerWithHash<Self> + Marker traits` as KeyContainer in [`Bounds`] trait.
pub trait ContainerWithHash<B: Bounds> {
    fn as_dyn_hash(&self) -> &dyn DynHash;

    fn as_container(&self) -> &B::Container;
    fn as_mut_container(&mut self) -> &mut B::Container;
    fn into_box_container(self: Box<Self>) -> Box<B::Container>;
}

impl<B: Bounds + HasBounds<K>, K: 'static + Hash + Eq> ContainerWithHash<B> for K {
    fn as_dyn_hash(&self) -> &dyn DynHash {
        self
    }

    fn as_container(&self) -> &B::Container {
        B::as_ref(self)
    }
    fn as_mut_container(&mut self) -> &mut B::Container {
        B::as_mut(self)
    }
    fn into_box_container(self: Box<Self>) -> Box<B::Container> {
        B::cast_box(self)
    }
}

/// Default bounds for TypedMap that require keys/values just to implement `Any`.
pub struct AnyBounds;

impl Bounds for AnyBounds {
    type KeyContainer = dyn ContainerWithHash<AnyBounds>;
    type Container = dyn Any;

    fn as_any(this: &Self::Container) -> &dyn Any {
        this
    }

    fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any {
        this
    }

    fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any> {
        this
    }
}

impl<T: 'static> HasBounds<T> for AnyBounds {
    fn cast_box(this: Box<T>) -> Box<Self::Container> {
        this
    }

    fn as_ref(this: &T) -> &Self::Container {
        this
    }

    fn as_mut(this: &mut T) -> &mut Self::Container {
        this
    }

    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        this
    }
}

/// Default bounds for TypedDashMap that require keys/values just to implement `Any + Send + Sync`.
pub struct SyncAnyBounds;

impl Bounds for SyncAnyBounds {
    type KeyContainer = dyn ContainerWithHash<SyncAnyBounds> + Send + Sync;
    type Container = dyn Any + Send + Sync;

    fn as_any(this: &Self::Container) -> &dyn Any {
        this
    }

    fn as_any_mut(this: &mut Self::Container) -> &mut dyn Any {
        this
    }

    fn as_any_box(this: Box<Self::Container>) -> Box<dyn Any> {
        this
    }
}

impl<T: 'static + Send + Sync> HasBounds<T> for SyncAnyBounds {
    fn cast_box(this: Box<T>) -> Box<Self::Container> {
        this
    }

    fn as_ref(this: &T) -> &Self::Container {
        this
    }

    fn as_mut(this: &mut T) -> &mut Self::Container {
        this
    }

    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        this
    }
}
