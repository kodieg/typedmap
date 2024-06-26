//! Restricting types that may be stored in the hashmap.
//!
//! Struct that implement [`Bounds`] trait may be used as a restriction on types for keys or values
//! stored in the hashmap. Imagine that you'd like to store only values that implement some trait, e.g.
//! service. One can implement new bounds using convenience macros [impl_custom_bounds](crate::impl_custom_bounds) and [impl_dyn_trait_wrapper](crate::impl_dyn_trait_wrapper):
//! ```rust
//! use std::any::Any;
//! use std::hash::Hash;
//! use typedmap::bounds::{Bounds, ContainerWithHash, HasBounds};
//! use typedmap::{AnyBounds, impl_custom_bounds, impl_dyn_trait_wrapper, TypedMap, TypedMapKey};
//!
//! // Your trait that map values must implement
//! trait Service {
//!     fn is_ready(&self) -> bool;
//! }
//!
//! // You need a struct to represent bounds requirement
//! struct ServiceBounds;
//!
//! // Implement a trait object type DynService to be stored in map and represent Service trait
//! impl_dyn_trait_wrapper!(DynService, Service);
//! // Implement Bounds trait & HasBounds<T> for ServiceBounds
//! impl_custom_bounds!(ServiceBounds, DynService, Service);
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
//!    let _ = kv.value_container_ref().as_object().is_ready();
//! }
//!
//! ```
//!
//! Manually one can do it in the following way:
//! ```rust
//! use std::any::Any;
//! use std::hash::Hash;
//! use typedmap::bounds::{Bounds, ContainerWithHash, HasBounds};
//! use typedmap::{AnyBounds, impl_custom_bounds, impl_dyn_trait_wrapper, TypedMap, TypedMapKey};
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
//! trait DynService: Any + Service {
//!     fn as_object(&self) -> &dyn Service;
//!
//!     fn as_any(&self) -> &dyn Any;
//!     fn as_mut_any(&mut self) -> &mut dyn Any;
//!     fn as_box_any(self: Box<Self>) -> Box<dyn Any>;
//! }
//!
//! impl<T: Service + Any> DynService for T {
//!     fn as_object(&self) -> &dyn Service {
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
//!    let _ = kv.value_container_ref().as_object().is_ready();
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
    /// Converts from `Box<T>` to `Box<Container>`
    fn cast_box(this: Box<T>) -> Box<Self::Container>;
    /// Converts from `&T` to `&Container`
    fn as_ref(this: &T) -> &Self::Container;
    /// Converts from `&mut T` to `&mut Container`
    fn as_mut(this: &mut T) -> &mut Self::Container;

    /// Converts from `Box<T>` to `Box<KeyContainer>`
    fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq;

    /// Boxes key of type `T` as `Box<KeyContainer>`
    fn box_key(this: T) -> Box<Self::KeyContainer>
    where
        T: 'static + Sized + Hash + Eq,
    {
        Self::cast_key_box(Box::new(this))
    }

    /// Boxes value of type `T` as `Box<Container>`
    fn box_value(this: T) -> Box<Self::Container>
    where
        Self: Sized,
    {
        Self::cast_box(Box::new(this))
    }

    /// Attempts to downcast `&Container` to `&T`
    fn downcast_ref(this: &Self::Container) -> Option<&T>
    where
        Self: 'static + Sized,
    {
        let any = Self::as_any(this);
        any.downcast_ref()
    }

    /// Attempts to downcast `&mut Container` to `&mut T`
    fn downcast_mut(this: &mut Self::Container) -> Option<&mut T>
    where
        Self: 'static + Sized,
    {
        let any = Self::as_any_mut(this);
        any.downcast_mut()
    }

    /// Attempts to downcast `Box<Container>` to `Box<T>`
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

/// Implements DynTrait `$dyn` wrapper for specified trait `$trait_name`.
///
/// DynTrait exposes reference to dyn `$trait_name` using `as_object` method. It also exposes necessary
/// conversions to [Any](std::any::Any) trait.
///
/// For example, you can define DynComponent trait that will inherit from both Component and Any:
/// ```rust
/// use typedmap::impl_dyn_trait_wrapper;
/// trait Component {}
/// impl_dyn_trait_wrapper!(DynComponent, Component);
/// ```
/// which expands to
/// ```rust
/// # trait Component {}
/// trait DynComponent: ::std::any::Any {
///     fn as_object(&self) -> &(dyn Component);
///
///     fn as_any(&self) -> &dyn ::std::any::Any;
///     fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any;
///     fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any>;
/// }
/// impl<T: Component + ::std::any::Any> DynComponent for T {
///     fn as_object(&self) -> &(dyn Component) {
///         self
///     }
///
///     fn as_any(&self) -> &dyn ::std::any::Any {
///         self
///     }
///
///     fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any {
///         self
///     }
///
///     fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any> {
///         self
///     }
/// }
/// ```
///
///
/// Optionally you can specify additionally marker traits, e.g. Send+Sync, for example:
/// ```rust
/// use typedmap::impl_dyn_trait_wrapper;
/// trait Component {}
/// impl_dyn_trait_wrapper!(DynComponent, Component, +Send+Sync);
/// ```
/// which expands to
/// ```rust
/// # trait Component {}
/// trait DynComponent: ::std::any::Any + Send + Sync {
///     fn as_object(&self) -> &(dyn Component + Send + Sync);
///
///     fn as_any(&self) -> &dyn ::std::any::Any;
///     fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any;
///     fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any>;
/// }
/// impl<T: Component + ::std::any::Any + Send + Sync> DynComponent for T {
///     fn as_object(&self) -> &(dyn Component + Send + Sync) {
///         self
///     }
///
///     fn as_any(&self) -> &dyn ::std::any::Any {
///         self
///     }
///
///     fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any {
///         self
///     }
///
///     fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any> {
///         self
///     }
/// }
/// ```
/// This DynTrait wrapper can be used as a [`Bounds::Container`] in [`Bounds`] implementation.
///
#[macro_export]
macro_rules! impl_dyn_trait_wrapper {
    ($dyn:ident, $trait_name:ident) => {
        $crate::impl_dyn_trait_wrapper!($dyn, $trait_name, );
    };
    ($dyn:ident, $trait_name:ident, $(+ $marker_traits:ident)*) => {
        trait $dyn: ::std::any::Any $(+ $marker_traits)*{
            fn as_object(&self) -> &(dyn $trait_name $(+ $marker_traits)*);

            fn as_any(&self) -> &dyn ::std::any::Any;
            fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any;
            fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any>;
        }

        impl<T: $trait_name + ::std::any::Any $(+ $marker_traits)*> $dyn for T {
            fn as_object(&self) -> &(dyn $trait_name $(+ $marker_traits)*) {
                self
            }

            fn as_any(&self) -> &dyn ::std::any::Any {
                self
            }

            fn as_mut_any(&mut self) -> &mut dyn ::std::any::Any {
                self
            }

            fn as_any_box(self: Box<Self>) -> Box<dyn ::std::any::Any> {
                self
            }
        }
    }
}

/// Implements [`Bounds`] & [`HasBounds`] traits for `$bounds` using `$dyn` trait object and wrapping `$trait_name`.
/// Together with [impl_dyn_trait_wrapper](crate::impl_dyn_trait_wrapper) macro, it serves as simple way to implement custom [`Bounds`].
///
/// For example you may define requirement for custom trait `Component`. Firstly, you need to define trait object
/// that will be both `Any` and `Component`. Easiest way to do it is to use [`impl_dyn_trait_wrapper`].
/// Then you need to define bounds struct and use `impl_custom_bounds` macro.
/// ```rust
/// use std::any::Any;
/// use typedmap::{impl_custom_bounds, impl_dyn_trait_wrapper};
///
/// // Trait that you require
/// trait Component {}
/// // Requirement bounds used in TypedMap or TypedDashMap
/// struct CustomBounds;
/// impl_dyn_trait_wrapper!(DynComponent, Component);
/// impl_custom_bounds!(CustomBounds, DynComponent, Component);
/// ```
/// `impl_custom_bounds` expands to:
/// ```rust
/// # use std::any::Any;
/// # use typedmap::{impl_custom_bounds, impl_dyn_trait_wrapper};
/// # trait Component {}
/// # impl_dyn_trait_wrapper!(DynComponent, Component);
/// # struct CustomBounds;
/// impl ::typedmap::bounds::Bounds for CustomBounds {
///     type KeyContainer = dyn ::typedmap::bounds::ContainerWithHash<CustomBounds>;
///     type Container = dyn DynComponent;
///
///     fn as_any(this: &Self::Container) -> &dyn ::std::any::Any {
///         this.as_any()
///     }
///
///     fn as_any_mut(this: &mut Self::Container) -> &mut dyn ::std::any::Any {
///         this.as_mut_any()
///     }
///
///     fn as_any_box(this: Box<Self::Container>) -> Box<dyn ::std::any::Any> {
///         this.as_any_box()
///     }
/// }
/// impl<T: Component + ::std::any::Any> ::typedmap::bounds::HasBounds<T> for CustomBounds {
///     fn cast_box(this: Box<T>) -> Box<Self::Container> {
///         this
///     }
///
///     fn as_ref(this: &T) -> &Self::Container {
///         this
///     }
///
///     fn as_mut(this: &mut T) -> &mut Self::Container {
///         this
///     }
///
///     fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer> where T: 'static + Sized + ::std::hash::Hash + ::std::cmp::Eq {
///         this
///     }
/// }
/// ```
///
/// You can also add marker traits as requrement, for example:
/// ```rust
/// # use std::any::Any;
/// # use typedmap::{impl_custom_bounds, impl_dyn_trait_wrapper};
/// # trait Component {}
/// # struct CustomBounds;
/// # impl_dyn_trait_wrapper!(DynComponent, Component);
/// impl_custom_bounds!(CustomBounds, DynComponent, Component, +Send+Sync);
/// ```
/// which expands to:
/// ```rust
/// # use std::any::Any;
/// # use typedmap::{impl_custom_bounds, impl_dyn_trait_wrapper};
/// # trait Component {}
/// # struct CustomBounds;
/// # impl_dyn_trait_wrapper!(DynComponent, Component);
/// impl ::typedmap::bounds::Bounds for CustomBounds {
///     type KeyContainer = dyn ::typedmap::bounds::ContainerWithHash<CustomBounds> + Send + Sync;
///     type Container = dyn DynComponent + Send + Sync;
///
///     fn as_any(this: &Self::Container) -> &dyn ::std::any::Any {
///         this.as_any()
///     }
///
///     fn as_any_mut(this: &mut Self::Container) -> &mut dyn ::std::any::Any {
///         this.as_mut_any()
///     }
///
///     fn as_any_box(this: Box<Self::Container>) -> Box<dyn ::std::any::Any> {
///         this.as_any_box()
///     }
/// }
/// impl<T: Component + ::std::any::Any + Send + Sync> ::typedmap::bounds::HasBounds<T> for CustomBounds {
///     fn cast_box(this: Box<T>) -> Box<Self::Container> {
///         this
///     }
///
///     fn as_ref(this: &T) -> &Self::Container {
///         this
///     }
///
///     fn as_mut(this: &mut T) -> &mut Self::Container {
///         this
///     }
///
///     fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer> where T: 'static + Sized + ::std::hash::Hash + ::std::cmp::Eq {
///         this
///     }
/// }
/// ```
///
#[macro_export]
macro_rules! impl_custom_bounds {
    ($bounds:ident, $dyn:ident, $trait_name:ident) => {
        $crate::impl_custom_bounds!($bounds, $dyn, $trait_name, );
    };
    ($bounds:ident, $dyn:ident, $trait_name:ident, $(+ $marker_traits:ident)*) => {
        $crate::impl_custom_bounds_with_key_container!($bounds, $dyn, dyn $crate::bounds::ContainerWithHash<$bounds> $(+ $marker_traits)*, $trait_name, $(+ $marker_traits)*);
    }
}

/// Implements [`Bounds`] & [`HasBounds`] traits for `$bounds` using `$dyn` trait object and wrapping `$trait_name` specifying KeyContainer with `$key_container`.
/// Together with [impl_dyn_trait_wrapper](crate::impl_dyn_trait_wrapper) macro, it serves as simple way to implement custom [`Bounds`].
///
/// For example see how [ContainerWithHashAndClone](crate::clone::ContainerWithHashAndClone) is used as KeyContainer to allow key to be cloneable.
#[macro_export]
macro_rules! impl_custom_bounds_with_key_container {
    ($bounds:ident, $dyn:ident, $key_container:ty, $trait_name:ident) => {
        $crate::impl_custom_bounds_with_key_container!($bounds, $dyn, $key_container, $trait_name, );
    };
    ($bounds:ident, $dyn:ident, $key_container:ty, $trait_name:ident, $(+ $marker_traits:ident)*) => {
        impl $crate::bounds::Bounds for $bounds {
            type KeyContainer = $key_container;
            type Container = dyn $dyn $(+ $marker_traits)*;

            fn as_any(this: &Self::Container) -> &dyn ::std::any::Any {
                this.as_any()
            }

            fn as_any_mut(this: &mut Self::Container) -> &mut dyn ::std::any::Any {
                this.as_mut_any()
            }

            fn as_any_box(this: Box<Self::Container>) -> Box<dyn ::std::any::Any> {
                this.as_any_box()
            }
        }

        impl<T: $trait_name + ::std::any::Any $(+ $marker_traits)*> $crate::bounds::HasBounds<T> for $bounds {
            fn cast_box(this: Box<T>) -> Box<Self::Container> {
                this
            }

            fn as_ref(this: &T) -> &Self::Container {
                this
            }

            fn as_mut(this: &mut T) -> &mut Self::Container {
                this
            }

            fn cast_key_box(this: Box<T>) -> Box<Self::KeyContainer> where T: 'static + Sized + ::std::hash::Hash + ::std::cmp::Eq {
                this
            }
        }
    }
}
