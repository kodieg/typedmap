use std::any::Any;

pub(crate) struct TypedMapValueBase<T: ?Sized + 'static + Any = dyn Any + 'static>(Box<T>);
pub(crate) type TypedMapValue = TypedMapValueBase<dyn Any + 'static>;
pub(crate) type SyncTypedMapValue = TypedMapValueBase<dyn Any + Send + Sync + 'static>;

impl TypedMapValueBase<dyn Any + 'static> {
    pub fn from_value<V: Any + 'static>(value: V) -> Self {
        Self(Box::new(value))
    }

    pub fn as_any(&self) -> &dyn Any {
        self.0.as_ref()
    }

    pub fn as_mut_any(&mut self) -> &mut dyn Any {
        self.0.as_mut()
    }
}

impl TypedMapValueBase<dyn Any + 'static> {
    pub fn downcast<V: Any>(self) -> Result<V, Self> {
        let boxed: Box<dyn Any + 'static> = self.0;
        let boxed: Result<Box<V>, _> = boxed.downcast();
        boxed.map(|v| *v).map_err(|dyn_value| Self(dyn_value))
    }

    pub fn downcast_ref<V: Any>(&self) -> Option<&V> {
        self.0.as_ref().downcast_ref::<V>()
    }

    pub fn is<V: 'static + Any>(&self) -> bool {
        self.0.as_ref().is::<V>()
    }

    pub fn downcast_mut<V: 'static + Any>(&mut self) -> Option<&mut V> {
        self.0.as_mut().downcast_mut::<V>()
    }
}

impl TypedMapValueBase<dyn Any + Send + Sync + 'static> {
    pub fn from_value<V: Any + Send + Sync + 'static>(value: V) -> Self {
        Self(Box::new(value))
    }

    pub fn downcast<V: Any>(self) -> Option<V> {
        let boxed: Box<dyn Any + 'static> = self.0;
        let boxed: Option<Box<V>> = boxed.downcast().ok();
        boxed.map(|v| *v)
    }

    pub fn downcast_ref<V: Any>(&self) -> Option<&V> {
        self.0.as_ref().downcast_ref::<V>()
    }

    pub fn downcast_mut<V: Any>(&mut self) -> Option<&mut V> {
        self.0.as_mut().downcast_mut::<V>()
    }
}
