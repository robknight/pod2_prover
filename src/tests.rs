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
    
    // X = Y, Y = Z
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));
    
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("Y", "Y"),
        make_anchored_key("Z", "Z")
    ));

    // Try to prove X = Z
    engine.set_target(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("Z", "Z")
    ));

    let proofs = engine.prove();
    assert!(!proofs.is_empty(), "Should be able to prove X = Z");
    
    // Check that we used transitive equality
    let (_, chain) = &proofs[0];
    assert_eq!(chain.len(), 1, "Should have exactly one deduction step");
    let (op_code, inputs, output) = &chain[0];
    assert_eq!(*op_code, NativeOperation::TransitiveEqualFromStatements as u8, 
        "Should use TransitiveEqualFromStatements operation");
    assert_eq!(inputs.len(), 2, "Should use exactly two input statements");
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