use crate::types::*;
use ascent::ascent;
use pod2::frontend::AnchoredKey;
use pod2::middleware::{hash_str, NativeOperation, Value as MiddlewareValue};

use super::types::WildcardStatement;

// Helper function to convert HashableValue to Value
fn to_value(hv: &HashableValue) -> MiddlewareValue {
    match hv {
        HashableValue::Int(i) => MiddlewareValue::from(*i),
        HashableValue::String(s) => MiddlewareValue::from(hash_str(s)),
        HashableValue::Bool(b) => MiddlewareValue::from(if *b { 1i64 } else { 0i64 }),
        HashableValue::Array(arr) => arr.commitment().value(),
        HashableValue::Set(set) => set.commitment().value(),
        HashableValue::Dictionary(dict) => dict.commitment().value(),
    }
}

// Helper function to check if one value contains another
// Supports arrays and sets, returns false for other types
fn check_contains(container: &HashableValue, contained: &HashableValue) -> bool {
    match (container, contained) {
        // For arrays, check if the contained value is an element
        (HashableValue::Array(arr), value) => {
            let value = to_value(value);
            // Check each element in the array using the iterator
            for (_, elem) in arr.iter() {
                if elem == &value {
                    return true;
                }
            }
            false
        },
        
        // For sets, check if the contained value is a member
        (HashableValue::Set(set), value) => {
            let value = to_value(value);
            set.contains(&value).unwrap_or(false)
        },
        
        // For other types, containment is not defined
        _ => false,
    }
}

// Main deduction engine that handles proof generation
pub struct DeductionEngine {
    prog: AscentProgram,
}

impl DeductionEngine {
    pub fn new() -> Self {
        Self {
            prog: AscentProgram::default(),
        }
    }

    // Add a known fact to the engine
    pub fn add_fact(&mut self, fact: HashableStatement) {
        self.prog.known_statement.push((fact,));
    }

    // Set the target statement we're trying to prove
    pub fn set_target(&mut self, target: WildcardStatement) {
        self.prog.target_statement = vec![(target,)];
    }

    // Run the deduction engine and return all proofs found
    pub fn prove(&mut self) -> Vec<(HashableStatement, DeductionChain)> {
        self.prog.run();
        self.prog.can_prove.clone()
    }

    // Print a human-readable proof chain
    pub fn print_proof(&self, statement: HashableStatement, chain: DeductionChain) {
        println!("\nProved: {}", statement);
        if chain.is_empty() {
            println!("This statement was directly known (no deduction needed)");
            return;
        }

        println!("\nProof steps:");
        for (step, (op_code, inputs, output)) in chain.iter().enumerate() {
            println!("\nStep {}:", step + 1);
            println!("Operation: {}", operation_name(*op_code));
            println!("From:");
            for input in inputs {
                println!("  - {}", input);
            }
            println!("Deduced:");
            println!("  => {}", output);
        }
    }
}

ascent! {
    // Core relations that track our knowledge and goals
    relation known_statement(HashableStatement);  // Statements we know to be true
    relation target_statement(WildcardStatement);  // The statement we're trying to prove
    relation can_prove(HashableStatement, DeductionChain);  // Statements we can prove with their proof chains
    relation known_value(AnchoredKey, HashableValue);  // Values we know for specific keys
    relation known_equal(AnchoredKey, AnchoredKey);  // Known equality relationships
    relation known_gt(AnchoredKey, AnchoredKey);  // Known greater-than relationships
    relation known_lt(AnchoredKey, AnchoredKey);  // Known less-than relationships
    relation known_neq(AnchoredKey, AnchoredKey);  // Known not-equal relationships
    relation known_contains(AnchoredKey, AnchoredKey);  // Known contains relationships
    relation reachable_equal(AnchoredKey, AnchoredKey, DeductionChain);  // Equality relationships we can prove through chains
    relation connected_to_target(AnchoredKey, AnchoredKey, DeductionChain);  // Chains that connect to our target statement

    // Base case: directly match known statements with wildcard targets
    can_prove(stmt, chain) <--
        target_statement(wild_stmt),
        known_statement(known_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = wild_stmt,
        if let HashableStatement::Equal(known_key, known_concrete) = known_stmt,
        if wild_key.matches(&known_key) && concrete_key == known_concrete,
        let stmt = known_stmt.clone(),
        let chain = vec![];

    // Prove equality through chains of known equalities
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Equal(found_key.clone(), concrete_key.clone());

    // Prove greater-than relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Gt(found_key.clone(), concrete_key.clone());

    // Prove less-than relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Lt(found_key.clone(), concrete_key.clone());

    // Prove not-equal relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::NotEqual(found_key.clone(), concrete_key.clone());

    // Prove contains relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Contains(found_key.clone(), concrete_key.clone());

    // Extract value assignments from known statements
    known_value(ak, v) <--
        known_statement(stmt),
        if let HashableStatement::ValueOf(ak, v) = stmt;

    // Extract equality relationships from known statements
    known_equal(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Equal(ak1, ak2) = stmt;

    // Extract greater-than relationships from known statements
    known_gt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Gt(ak1, ak2) = stmt;

    // Extract less-than relationships from known statements
    known_lt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Lt(ak1, ak2) = stmt;

    // Extract not-equal relationships from known statements
    known_neq(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::NotEqual(ak1, ak2) = stmt;

    // Extract contains relationships from known statements
    known_contains(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Contains(ak1, ak2) = stmt;

    // Base case: directly known equalities are reachable with empty chain
    reachable_equal(x, y, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Also add the reverse direction for known equalities (equality is symmetric)
    reachable_equal(y, x, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Build chains of equalities through transitivity (if a=b and b=c, then a=c)
    reachable_equal(x, z, new_chain) <--
        reachable_equal(x, y, chain1),
        known_equal(y, z),
        // Check that z isn't already in our chain to avoid cycles
        if !chain1.iter().any(|(_, _, output)|
            matches!(output, HashableStatement::Equal(_, ref end) if end == z)),
        let new_chain = {
            let mut chain = chain1.clone();
            chain.push((
                NativeOperation::TransitiveEqualFromStatements as u8,
                vec![
                    HashableStatement::Equal(x.clone(), y.clone()),
                    HashableStatement::Equal(y.clone(), z.clone())
                ],
                HashableStatement::Equal(x.clone(), z.clone())
            ));
            chain
        };

    // Find chains that connect to our target key for equality statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = stmt,
        reachable_equal(x, y, chain),
        if y == concrete_key;

    // Find chains for greater-than relationships:
    // 1. Direct value comparisons (e.g., 10 > 5)
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if let HashableValue::Int(i1) = v1,
        if let HashableValue::Int(i2) = v2,
        if i1 > i2,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::GtFromEntries as u8,
            vec![
                HashableStatement::ValueOf(x.clone(), v1.clone()),
                HashableStatement::ValueOf(y.clone(), v2.clone())
            ],
            HashableStatement::Gt(x.clone(), y.clone())
        )];

    // 2. Existing greater-than statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Gt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for less-than relationships:
    // 1. Direct value comparisons (e.g., 5 < 10)
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if let HashableValue::Int(i1) = v1,
        if let HashableValue::Int(i2) = v2,
        if i1 < i2,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::LtFromEntries as u8,
            vec![
                HashableStatement::ValueOf(x.clone(), v1.clone()),
                HashableStatement::ValueOf(y.clone(), v2.clone())
            ],
            HashableStatement::Lt(x.clone(), y.clone())
        )];

    // 2. Existing less-than statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Lt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for not-equal relationships:
    // 1. Converting greater-than to not-equal (if a > b, then a ≠ b)
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Gt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::GtToNotEqual as u8,
            vec![HashableStatement::Gt(x.clone(), y.clone())],
            HashableStatement::NotEqual(x.clone(), y.clone())
        )];

    // 2. Converting less-than to not-equal (if a < b, then a ≠ b)
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Lt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::LtToNotEqual as u8,
            vec![HashableStatement::Lt(x.clone(), y.clone())],
            HashableStatement::NotEqual(x.clone(), y.clone())
        )];

    // 3. Existing not-equal statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::NotEqual(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for contains relationships:
    // 1. Direct value comparisons (checking if a value is in an array or set)
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if check_contains(&v1, &v2),
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::ContainsFromEntries as u8,
            vec![
                HashableStatement::ValueOf(x.clone(), v1.clone()),
                HashableStatement::ValueOf(y.clone(), v2.clone())
            ],
            HashableStatement::Contains(x.clone(), y.clone())
        )];

    // 2. Existing contains statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Contains(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];
}
