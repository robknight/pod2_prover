use pod2::middleware::NativeOperation;
use pod2::middleware::containers::{Dictionary, Set, Array};
use pod2::frontend::AnchoredKey;


use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HashableStatement {
    None,
    ValueOf(AnchoredKey, HashableValue),
    Equal(AnchoredKey, AnchoredKey),
    NotEqual(AnchoredKey, AnchoredKey),
    Gt(AnchoredKey, AnchoredKey),
    Lt(AnchoredKey, AnchoredKey),
    Contains(AnchoredKey, AnchoredKey),
    NotContains(AnchoredKey, AnchoredKey),
    SumOf(AnchoredKey, AnchoredKey, AnchoredKey),
    ProductOf(AnchoredKey, AnchoredKey, AnchoredKey),
    MaxOf(AnchoredKey, AnchoredKey, AnchoredKey),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HashableValue {
    String(String),
    Int(i64),
    Bool(bool),
    Dictionary(Dictionary),
    Set(Set),
    Array(Array),
}

impl Hash for HashableValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the discriminant first
        std::mem::discriminant(self).hash(state);
        
        // Hash the inner values only for types that implement Hash
        match self {
            HashableValue::String(s) => s.hash(state),
            HashableValue::Int(i) => i.hash(state),
            HashableValue::Bool(b) => b.hash(state),
            // TODO: Implement hash for Dictionary, Set, and Array
            HashableValue::Dictionary(_) => {},
            HashableValue::Set(_) => {},
            HashableValue::Array(_) => {},
        }
    }
}

pub type DeductionStep = (u8, Vec<HashableStatement>, HashableStatement);
pub type DeductionChain = Vec<DeductionStep>;

// Helper function to format AnchoredKey
fn format_anchored_key(ak: &AnchoredKey) -> String {
    ak.1.to_string()  // Just show the key part
}

// impl HashableStatement {
//     pub fn from_statement(stmt: &Statement) -> Option<Self> {
//         match stmt {
//             Statement::None => Some(Self::None),
//             Statement::ValueOf(ak, v) => Some(Self::ValueOf(*ak, *v)),
//             Statement::Equal(ak1, ak2) => Some(Self::Equal(*ak1, *ak2)),
//             Statement::NotEqual(ak1, ak2) => Some(Self::NotEqual(*ak1, *ak2)),
//             Statement::Gt(ak1, ak2) => Some(Self::Gt(*ak1, *ak2)),
//             Statement::Lt(ak1, ak2) => Some(Self::Lt(*ak1, *ak2)),
//             Statement::Contains(ak1, ak2) => Some(Self::Contains(*ak1, *ak2)),
//             Statement::NotContains(ak1, ak2) => Some(Self::NotContains(*ak1, *ak2)),
//             Statement::SumOf(ak1, ak2, ak3) => Some(Self::SumOf(*ak1, *ak2, *ak3)),
//             Statement::ProductOf(ak1, ak2, ak3) => Some(Self::ProductOf(*ak1, *ak2, *ak3)),
//             Statement::MaxOf(ak1, ak2, ak3) => Some(Self::MaxOf(*ak1, *ak2, *ak3)),
//             Statement::Custom(_, _) => None,
//         }
//     }

//     pub fn into_statement(self) -> Statement {
//         match self {
//             Self::None => Statement::None,
//             Self::ValueOf(ak, v) => Statement::ValueOf(ak, v),
//             Self::Equal(ak1, ak2) => Statement::Equal(ak1, ak2),
//             Self::NotEqual(ak1, ak2) => Statement::NotEqual(ak1, ak2),
//             Self::Gt(ak1, ak2) => Statement::Gt(ak1, ak2),
//             Self::Lt(ak1, ak2) => Statement::Lt(ak1, ak2),
//             Self::Contains(ak1, ak2) => Statement::Contains(ak1, ak2),
//             Self::NotContains(ak1, ak2) => Statement::NotContains(ak1, ak2),
//             Self::SumOf(ak1, ak2, ak3) => Statement::SumOf(ak1, ak2, ak3),
//             Self::ProductOf(ak1, ak2, ak3) => Statement::ProductOf(ak1, ak2, ak3),
//             Self::MaxOf(ak1, ak2, ak3) => Statement::MaxOf(ak1, ak2, ak3),
//         }
//     }
// }

impl fmt::Display for HashableValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HashableValue::String(s) => write!(f, "{}", s),
            HashableValue::Int(i) => write!(f, "{}", i),
            HashableValue::Bool(b) => write!(f, "{}", b),
            HashableValue::Dictionary(d) => write!(f, "{:?}", d),
            HashableValue::Set(s) => write!(f, "{:?}", s),
            HashableValue::Array(a) => write!(f, "{:?}", a),
        }
    }
}


impl fmt::Display for HashableStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => write!(f, "None"),
            Self::ValueOf(ak, v) => write!(f, "{} = {}", format_anchored_key(ak), v),
            Self::Equal(ak1, ak2) => write!(f, "{} = {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::NotEqual(ak1, ak2) => write!(f, "{} ≠ {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::Gt(ak1, ak2) => write!(f, "{} > {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::Lt(ak1, ak2) => write!(f, "{} < {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::Contains(ak1, ak2) => write!(f, "{} contains {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::NotContains(ak1, ak2) => write!(f, "{} does not contain {}", format_anchored_key(ak1), format_anchored_key(ak2)),
            Self::SumOf(ak1, ak2, ak3) => write!(f, "{} = {} + {}", 
                format_anchored_key(ak1), format_anchored_key(ak2), format_anchored_key(ak3)),
            Self::ProductOf(ak1, ak2, ak3) => write!(f, "{} = {} × {}", 
                format_anchored_key(ak1), format_anchored_key(ak2), format_anchored_key(ak3)),
            Self::MaxOf(ak1, ak2, ak3) => write!(f, "{} = max({}, {})", 
                format_anchored_key(ak1), format_anchored_key(ak2), format_anchored_key(ak3)),
        }
    }
}

pub fn operation_name(op_code: u8) -> &'static str {
    match op_code {
        x if x == NativeOperation::None as u8 => "None",
        x if x == NativeOperation::NewEntry as u8 => "NewEntry",
        x if x == NativeOperation::CopyStatement as u8 => "CopyStatement",
        x if x == NativeOperation::EqualFromEntries as u8 => "EqualFromEntries",
        x if x == NativeOperation::NotEqualFromEntries as u8 => "NotEqualFromEntries",
        x if x == NativeOperation::GtFromEntries as u8 => "GtFromEntries",
        x if x == NativeOperation::LtFromEntries as u8 => "LtFromEntries",
        x if x == NativeOperation::TransitiveEqualFromStatements as u8 => "TransitiveEqualFromStatements",
        x if x == NativeOperation::GtToNotEqual as u8 => "GtToNotEqual",
        x if x == NativeOperation::LtToNotEqual as u8 => "LtToNotEqual",
        x if x == NativeOperation::ContainsFromEntries as u8 => "ContainsFromEntries",
        x if x == NativeOperation::NotContainsFromEntries as u8 => "NotContainsFromEntries",
        x if x == NativeOperation::SumOf as u8 => "SumOf",
        x if x == NativeOperation::ProductOf as u8 => "ProductOf",
        x if x == NativeOperation::MaxOf as u8 => "MaxOf",
        _ => "Unknown Operation"
    }
} 