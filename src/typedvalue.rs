use std::any::Any;
use std::fmt::{Debug, Formatter};

use crate::bounds::{Bounds, HasBounds};

pub(crate) struct TypedMapValue<B: Bounds>(Box<B::Container>);

impl<B: 'static + Bounds> TypedMapValue<B> {
    pub fn from_value<V: 'static>(value: V) -> Self
    where
        B: HasBounds<V>,
    {
        Self(B::box_value(value))
    }

    pub fn as_any(&self) -> &dyn Any {
        B::as_any(&self.0)
    }

    pub fn as_mut_any(&mut self) -> &mut dyn Any {
        B::as_any_mut(&mut self.0)
    }

    pub fn downcast<V: 'static>(self) -> Result<V, Self>
    where
        B: HasBounds<V>,
    {
        if self.is::<V>() {
            Ok(*B::downcast_box(self.0).unwrap_or_else(|_| panic!("downcast failed")))
        } else {
            Err(self)
        }
    }

    pub fn downcast_ref<V: 'static>(&self) -> Option<&V>
    where
        B: HasBounds<V>,
    {
        B::downcast_ref(&self.0)
    }

    pub fn downcast_mut<V: 'static>(&mut self) -> Option<&mut V>
    where
        B: HasBounds<V>,
    {
        B::downcast_mut(&mut self.0)
    }

    pub fn is<V: 'static>(&self) -> bool
    where
        B: HasBounds<V>,
    {
        B::as_any(&self.0).is::<V>()
    }

    pub fn as_container(&self) -> &B::Container {
        &self.0
    }

    pub fn as_mut_container(&mut self) -> &mut B::Container {
        &mut self.0
    }

    pub fn into_box_container(self) -> Box<B::Container> {
        self.0
    }
}

impl<B: 'static + Bounds> Debug for TypedMapValue<B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("TypedMapValue")
    }
}
