use crate::{DeductionEngine, HashableStatement};
use pod2::middleware::{PodId, hash_str, NativeOperation};
use pod2::frontend::{AnchoredKey, Origin, PodClass, Value};

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
        make_anchored_key("Y", "Y")
    ));
    
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("Y", "Y"),
        make_anchored_key("Z", "Z")
    ));

    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("Z", "Z"),
        make_anchored_key("Q", "Q")
    ));

    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("Q", "Q"),
        make_anchored_key("W", "W")
    ));

    // Try to prove X = W
    engine.set_target(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("W", "W")
    ));



    let proofs = engine.prove();
    assert!(!proofs.is_empty(), "Should be able to prove X = W");
    
    // Check that we used transitive equality
    let (_, chain) = &proofs[0];
    assert_eq!(chain.len(), 3, "Should have exactly three deduction steps");
    let (op_code, inputs, output) = &chain[0];
    assert_eq!(*op_code, NativeOperation::TransitiveEqualFromStatements as u8, 
        "Should use TransitiveEqualFromStatements operation");
    assert_eq!(inputs.len(), 2, "Should use exactly three input statements");
}

#[test]
fn test_unprovable_statement() {
    let mut engine = DeductionEngine::new();
    
    // X = Y
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));

    // Try to prove X = Z (should fail - no information about Z)
    engine.set_target(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("Z", "Z")
    ));

    let proofs = engine.prove();
    assert!(proofs.is_empty(), "Should not be able to prove X = Z without information about Z");
}

#[test]
fn test_gt_to_not_equal() {
    let mut engine = DeductionEngine::new();
    
    // Given X > Y
    engine.add_fact(HashableStatement::Gt(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));

    // Try to prove X ≠ Y
    engine.set_target(HashableStatement::NotEqual(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));

    let proofs = engine.prove();
    assert!(!proofs.is_empty(), "Should be able to prove X ≠ Y from X > Y");
    
    // Check that we used GtToNotEqual
    let (_, chain) = &proofs[0];
    assert_eq!(chain.len(), 1, "Should have exactly one deduction step");
    let (op_code, inputs, output) = &chain[0];
    assert_eq!(*op_code, NativeOperation::GtToNotEqual as u8, 
        "Should use GtToNotEqual operation");
    assert_eq!(inputs.len(), 1, "Should use exactly one input statement");
    
    // Check that the input is the Gt statement
    match &inputs[0] {
        HashableStatement::Gt(ak1, ak2) => {
            assert_eq!(ak1.1, "X", "First key should be X");
            assert_eq!(ak2.1, "Y", "Second key should be Y");
        },
        _ => panic!("Input to GtToNotEqual must be a Gt statement")
    }
}

#[test]
fn test_lt_to_not_equal() {
    let mut engine = DeductionEngine::new();
    
    // Given X < Y
    engine.add_fact(HashableStatement::Lt(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));

    // Try to prove X ≠ Y
    engine.set_target(HashableStatement::NotEqual(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));

    let proofs = engine.prove();
    assert!(!proofs.is_empty(), "Should be able to prove X ≠ Y from X < Y");
    
    // Check that we used LtToNotEqual
    let (_, chain) = &proofs[0];
    assert_eq!(chain.len(), 1, "Should have exactly one deduction step");
    let (op_code, inputs, output) = &chain[0];
    assert_eq!(*op_code, NativeOperation::LtToNotEqual as u8, 
        "Should use LtToNotEqual operation");
    assert_eq!(inputs.len(), 1, "Should use exactly one input statement");
    
    // Check that the input is the Lt statement
    match &inputs[0] {
        HashableStatement::Lt(ak1, ak2) => {
            assert_eq!(ak1.1, "X", "First key should be X");
            assert_eq!(ak2.1, "Y", "Second key should be Y");
        },
        _ => panic!("Input to LtToNotEqual must be a Lt statement")
    }
}

#[test]
fn test_lt_and_gt_not_equal() {
    let mut engine = DeductionEngine::new();
    
    // Given X < Y and Y < Z
    engine.add_fact(HashableStatement::Lt(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));
    engine.add_fact(HashableStatement::Lt(
        make_anchored_key("Y", "Y"),
        make_anchored_key("Z", "Z")
    ));

    // Try to prove X ≠ Z - this should fail because POD2 doesn't support transitive Lt
    engine.set_target(HashableStatement::NotEqual(
        make_anchored_key("X", "X"),
        make_anchored_key("Z", "Z")
    ));

    let proofs = engine.prove();
    assert!(proofs.is_empty(), 
        "Should NOT be able to prove X ≠ Z because POD2 doesn't support transitive less than relationships yet");
}

#[test]
fn test_long_transitive_equality() {
    let mut engine = DeductionEngine::new();
    
    // Set up a long chain: A = B = C = D = E
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("A", "A"),
        make_anchored_key("B", "B")
    ));
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("B", "B"),
        make_anchored_key("C", "C")
    ));
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("C", "C"),
        make_anchored_key("D", "D")
    ));
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("D", "D"),
        make_anchored_key("E", "E")
    ));

    // Try to prove A = E (should work through the chain)
    engine.set_target(HashableStatement::Equal(
        make_anchored_key("A", "A"),
        make_anchored_key("E", "E")
    ));

    let proofs = engine.prove();
    assert!(!proofs.is_empty(), "Should be able to prove A = E");
    
    // Check that we found a proof
    let (stmt, chain) = &proofs[0];
    
    // Verify the statement connects A to E
    match stmt {
        HashableStatement::Equal(ak1, ak2) => {
            assert_eq!(ak1.1, "A", "First key should be A");
            assert_eq!(ak2.1, "E", "Second key should be E");
        },
        _ => panic!("Expected Equal statement")
    }
    
    // Verify we used multiple steps to get there
    assert!(chain.len() > 1, "Should require multiple steps to prove A = E");
    
    // Also try to prove E = A (should work due to symmetry)
    engine.set_target(HashableStatement::Equal(
        make_anchored_key("E", "E"),
        make_anchored_key("A", "A")
    ));
    
    let reverse_proofs = engine.prove();
    assert!(!reverse_proofs.is_empty(), "Should be able to prove E = A by symmetry");
} 