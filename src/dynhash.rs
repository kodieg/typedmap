use std::any::Any;
use std::hash::{Hash, Hasher};

// DynHash idea taken from here:
// https://www.reddit.com/r/rust/comments/cs6lfs/a_bunch_of_terrible_hacks_to_use_trait_objects_as/exdu7gg/?context=3
pub trait DynEq: Any {
    fn dyn_eq(&self, other: &dyn DynEq) -> bool;
    fn as_any(&self) -> &dyn Any;
    fn as_any_box(self: Box<Self>) -> Box<dyn Any>;
}

pub trait DynHash: DynEq {
    fn dyn_hash(&self, hasher: &mut dyn Hasher);
    fn as_dyn_eq(&self) -> &dyn DynEq;
}

impl<H: Eq + Any> DynEq for H {
    fn dyn_eq(&self, other: &dyn DynEq) -> bool {
        match other.as_any().downcast_ref::<H>() {
            Some(other) => self == other,
            None => false,
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_box(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

impl<H: Hash + DynEq> DynHash for H {
    fn dyn_hash(&self, mut hasher: &mut dyn Hasher) {
        H::hash(self, &mut hasher)
    }

    fn as_dyn_eq(&self) -> &dyn DynEq {
        self
    }
}

impl PartialEq for dyn DynHash {
    fn eq(&self, other: &dyn DynHash) -> bool {
        self.dyn_eq(other.as_dyn_eq())
    }
}

impl PartialEq for dyn DynHash + Send + Sync {
    fn eq(&self, other: &(dyn DynHash + Send + Sync)) -> bool {
        self.dyn_eq(other.as_dyn_eq())
    }
}

impl Eq for dyn DynHash {}
impl Eq for dyn DynHash + Send + Sync {}

impl Hash for dyn DynHash {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.dyn_hash(hasher)
    }
}

impl Hash for dyn DynHash + Send + Sync {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.dyn_hash(hasher)
    }
}
