use crate::types::*;
use ascent::ascent;
use pod2::frontend::{AnchoredKey, Origin, PodClass, Value as FrontendValue};
use pod2::middleware::{hash_str, NativeOperation, PodId, containers::Array as MiddlewareArray, Value as MiddlewareValue};

use super::types::{WildcardId, WildcardStatement};

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

// Stub function to check if a value is contained within another value
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

pub struct DeductionEngine {
    prog: AscentProgram,
}

impl DeductionEngine {
    pub fn new() -> Self {
        Self {
            prog: AscentProgram::default(),
        }
    }

    pub fn add_fact(&mut self, fact: HashableStatement) {
        self.prog.known_statement.push((fact,));
    }

    pub fn set_target(&mut self, target: WildcardStatement) {
        self.prog.target_statement = vec![(target,)];
    }

    pub fn prove(&mut self) -> Vec<(HashableStatement, DeductionChain)> {
        self.prog.run();
        self.prog.can_prove.clone()
    }

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
    // Keep only the core relations we need
    relation known_statement(HashableStatement);
    relation target_statement(WildcardStatement);
    relation can_prove(HashableStatement, DeductionChain);
    relation known_value(AnchoredKey, HashableValue);
    relation known_equal(AnchoredKey, AnchoredKey);
    relation known_gt(AnchoredKey, AnchoredKey);
    relation known_lt(AnchoredKey, AnchoredKey);
    relation known_neq(AnchoredKey, AnchoredKey);
    relation known_contains(AnchoredKey, AnchoredKey);
    relation reachable_equal(AnchoredKey, AnchoredKey, DeductionChain);
    relation connected_to_target(AnchoredKey, AnchoredKey, DeductionChain);

    // Remove all need_* relations and their rules

    // Keep the base case for direct matches
    can_prove(stmt, chain) <--
        target_statement(wild_stmt),
        known_statement(known_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = wild_stmt,
        if let HashableStatement::Equal(known_key, known_concrete) = known_stmt,
        if wild_key.matches(&known_key) && concrete_key == known_concrete,
        let stmt = known_stmt.clone(),
        let chain = vec![];

    // And keep the wildcard matching through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Equal(found_key.clone(), concrete_key.clone());

    // Add can_prove rule for GT statements
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Gt(found_key.clone(), concrete_key.clone());

    // Add can_prove rule for LT statements
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Lt(found_key.clone(), concrete_key.clone());

    // Add can_prove rule for NEq statements
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::NotEqual(found_key.clone(), concrete_key.clone());

    // Add can_prove rule for Contains statements
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = target_stmt,
        connected_to_target(found_key, _, chain),
        if wild_key.matches(&found_key),
        let stmt = HashableStatement::Contains(found_key.clone(), concrete_key.clone());

    // Extract relationships from known statements
    known_value(ak, v) <--
        known_statement(stmt),
        if let HashableStatement::ValueOf(ak, v) = stmt;

    known_equal(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Equal(ak1, ak2) = stmt;

    // Extract GT relationships from known statements
    known_gt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Gt(ak1, ak2) = stmt;

    // Extract LT relationships from known statements
    known_lt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Lt(ak1, ak2) = stmt;

    // Extract NEq relationships from known statements
    known_neq(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::NotEqual(ak1, ak2) = stmt;

    // Extract Contains relationships from known statements
    known_contains(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Contains(ak1, ak2) = stmt;

    // Base case: directly known equalities are reachable with empty chain
    reachable_equal(x, y, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Also add the reverse direction for known equalities
    reachable_equal(y, x, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Build chains one step at a time
    reachable_equal(x, z, new_chain) <--
        reachable_equal(x, y, chain1),
        known_equal(y, z),
        // Check that z isn't already in our chain
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

    // First find all chains that connect to our target key
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = stmt,
        reachable_equal(x, y, chain),
        if y == concrete_key;

    // Add GT to connected_to_target for:
    // 1. Direct value comparisons
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

    // 2. Existing GT statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Gt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Add LT to connected_to_target for:
    // 1. Direct value comparisons
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

    // 2. Existing LT statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::Lt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Add NEq to connected_to_target for:
    // 1. Converting GT to NEq
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

    // 2. Converting LT to NEq
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

    // 3. Existing NEq statements
    connected_to_target(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let HashableStatement::NotEqual(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Add Contains to connected_to_target for:
    // 1. Direct value comparisons
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

    // 2. Existing Contains statements
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wildcard::types::WildcardAnchoredKey;

    fn make_signed_origin(id: &str) -> Origin {
        Origin(PodClass::Signed, PodId(hash_str(id)))
    }

    fn make_anchored_key(id: &str, key: &str) -> AnchoredKey {
        AnchoredKey(make_signed_origin(id), key.to_string())
    }

    #[test]
    fn test_transitive_equality() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // X = Y, Y = Z, Z = Q, Q = W
        engine.add_fact(HashableStatement::Equal(
            make_anchored_key("X", "X"),
            make_anchored_key("Y", "Y"),
        ));

        engine.add_fact(HashableStatement::Equal(
            make_anchored_key("Y", "Y"),
            make_anchored_key("Z", "Z"),
        ));

        engine.add_fact(HashableStatement::Equal(
            make_anchored_key("Z", "Z"),
            make_anchored_key("Q", "Q"),
        ));

        engine.add_fact(HashableStatement::Equal(
            make_anchored_key("Q", "Q"),
            make_anchored_key("W", "W"),
        ));

        // Try to prove X = W
        engine.set_target(WildcardStatement::Equal(
            WildcardAnchoredKey(WildcardId::Named("X".to_string()), "X".to_string()),
            make_anchored_key("W", "W"),
        ));

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should be able to prove X = W");

        // Check that we used transitive equality
        let (_, chain) = &proofs[0];
        assert_eq!(chain.len(), 3, "Should have exactly three deduction steps");
        let (op_code, inputs, output) = &chain[0];
        assert_eq!(
            *op_code,
            NativeOperation::TransitiveEqualFromStatements as u8,
            "Should use TransitiveEqualFromStatements operation"
        );
        assert_eq!(inputs.len(), 2, "Should use exactly three input statements");
    }

    #[test]
    fn test_wildcard_gt() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // Add some values
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("X", "value"),
            HashableValue::Int(10),
        ));
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            HashableValue::Int(5),
        ));

        // Add a direct GT statement
        engine.add_fact(HashableStatement::Gt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find GT through value comparison
        let target = WildcardStatement::Gt(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should find X > Y through value comparison");
        let (stmt, chain) = &proofs[0];
        
        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());
        
        assert_eq!(chain.len(), 1, "Should use GtFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::GtFromEntries as u8,
            "Should use GtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            HashableStatement::Gt(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(target_key.1, "value", "Target key should have suffix 'value'");
            },
            _ => panic!("Expected Gt statement"),
        }
    }

    #[test]
    fn test_wildcard_lt() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // Add some values
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("X", "value"),
            HashableValue::Int(5),
        ));
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            HashableValue::Int(10),
        ));

        // Add a direct LT statement
        engine.add_fact(HashableStatement::Lt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find LT through value comparison
        let target = WildcardStatement::Lt(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should find X < Y through value comparison");
        let (stmt, chain) = &proofs[0];
        
        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());
        
        assert_eq!(chain.len(), 1, "Should use LtFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::LtFromEntries as u8,
            "Should use LtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            HashableStatement::Lt(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(target_key.1, "value", "Target key should have suffix 'value'");
            },
            _ => panic!("Expected Lt statement"),
        }
    }

    #[test]
    fn test_wildcard_neq() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // Add a GT statement that we'll convert to NEq
        engine.add_fact(HashableStatement::Gt(
            make_anchored_key("X", "value"),
            make_anchored_key("Y", "value"),
        ));

        // Add a direct NEq statement
        engine.add_fact(HashableStatement::NotEqual(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find NEq through GT conversion
        let target = WildcardStatement::NotEqual(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should find X != Y through GT conversion");
        let (stmt, chain) = &proofs[0];
        
        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());
        
        assert_eq!(chain.len(), 1, "Should use GtToNotEqual");
        assert_eq!(
            chain[0].0,
            NativeOperation::GtToNotEqual as u8,
            "Should use GtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            HashableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(target_key.1, "value", "Target key should have suffix 'value'");
            },
            _ => panic!("Expected NotEqual statement"),
        }
    }

    #[test]
    fn test_wildcard_neq_from_lt() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // Add an LT statement that we'll convert to NEq
        engine.add_fact(HashableStatement::Lt(
            make_anchored_key("X", "value"),
            make_anchored_key("Y", "value"),
        ));

        // Add a direct NEq statement
        engine.add_fact(HashableStatement::NotEqual(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find NEq through LT conversion
        let target = WildcardStatement::NotEqual(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should find X != Y through LT conversion");
        let (stmt, chain) = &proofs[0];
        
        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());
        
        assert_eq!(chain.len(), 1, "Should use LtToNotEqual");
        assert_eq!(
            chain[0].0,
            NativeOperation::LtToNotEqual as u8,
            "Should use LtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            HashableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(target_key.1, "value", "Target key should have suffix 'value'");
            },
            _ => panic!("Expected NotEqual statement"),
        }
    }

    #[test]
    fn test_wildcard_contains() {
        use crate::wildcard::types::WildcardAnchoredKey;

        let mut engine = DeductionEngine::new();

        // Add an array that contains a value
        let values = vec![
            MiddlewareValue::from(1i64),
            MiddlewareValue::from(2i64),
            MiddlewareValue::from(3i64),
        ];
        let arr = MiddlewareArray::new(&values).unwrap();
        
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("X", "value"),
            HashableValue::Array(arr),
        ));
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            HashableValue::Int(2),
        ));

        // Add a direct Contains statement
        engine.add_fact(HashableStatement::Contains(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find Contains through value comparison
        let target = WildcardStatement::Contains(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should find X contains Y through value comparison");
        let (stmt, chain) = &proofs[0];
        
        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());
        
        assert_eq!(chain.len(), 1, "Should use ContainsFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::ContainsFromEntries as u8,
            "Should use ContainsFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            HashableStatement::Contains(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(target_key.1, "value", "Target key should have suffix 'value'");
            },
            _ => panic!("Expected Contains statement"),
        }
    }
}
