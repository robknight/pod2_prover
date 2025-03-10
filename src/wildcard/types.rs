use pod2::frontend::{AnchoredKey, Origin};

use crate::types::HashableValue;

// The core wildcard type - represents either a concrete origin or a named wildcard
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WildcardId {
    Concrete(Origin),
    Named(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WildcardAnchoredKey(pub WildcardId, pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WildcardStatement {
    ValueOf(WildcardAnchoredKey, HashableValue),
    Equal(WildcardAnchoredKey, AnchoredKey),
    NotEqual(WildcardAnchoredKey, AnchoredKey),
    Gt(WildcardAnchoredKey, AnchoredKey),
    Lt(WildcardAnchoredKey, AnchoredKey),
    Contains(WildcardAnchoredKey, AnchoredKey),
}

// Helper methods for WildcardAnchoredKey
impl WildcardAnchoredKey {
    pub fn concrete(origin: Origin, key: String) -> Self {
        Self(WildcardId::Concrete(origin), key)
    }

    pub fn wildcard(key: String, name: impl Into<String>) -> Self {
        Self(WildcardId::Named(name.into()), key)
    }

    pub fn matches(&self, concrete: &AnchoredKey) -> bool {
        if let WildcardId::Concrete(origin) = &self.0 {
            return *origin == concrete.0 && self.1 == concrete.1;
        }

        if let WildcardId::Named(_) = &self.0 {
            return self.1 == concrete.1;
        }

        false
    }
}
