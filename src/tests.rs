
#[cfg(test)]
mod tests {
    use pod2::{frontend::{AnchoredKey, Origin, PodClass}, middleware::{containers::Array as MiddlewareArray, hash_str, NativeOperation, PodId, Value as MiddlewareValue}};

    use super::*;
    use crate::{engine::DeductionEngine, types::{HashableStatement, HashableValue, WildcardAnchoredKey, WildcardId, WildcardStatement}};

    fn make_signed_origin(id: &str) -> Origin {
        Origin(PodClass::Signed, PodId(hash_str(id)))
    }

    fn make_anchored_key(id: &str, key: &str) -> AnchoredKey {
        AnchoredKey(make_signed_origin(id), key.to_string())
    }

    #[test]
    fn test_transitive_equality() {

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
        let (stmt, chain) = &proofs[0];
        engine.print_proof(stmt.clone(), chain.clone());
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

    #[test]
    fn test_wildcard_contains_unprovable() {
        let mut engine = DeductionEngine::new();

        // Add an array that contains values 1, 2, 3
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
        // Add a value that is NOT in the array
        engine.add_fact(HashableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            HashableValue::Int(4),
        ));

        // Try to prove that X contains Y (which should be impossible)
        let target = WildcardStatement::Contains(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(proofs.is_empty(), "Should NOT be able to prove X contains Y since 4 is not in the array");
    }
}
