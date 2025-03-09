use ascent_pod2::{DeductionEngine, HashableStatement, HashableValue};
use pod2::middleware::{PodId, hash_str};
use pod2::frontend::{AnchoredKey, Origin, PodClass};

fn make_signed_origin(id: &str) -> Origin {
    Origin(PodClass::Signed, PodId(hash_str(id)))
}

fn make_anchored_key(id: &str, key: &str) -> AnchoredKey {
    AnchoredKey(make_signed_origin(id), key.to_string())
}

fn main() {
    let mut engine = DeductionEngine::new();

    // Add known facts
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("X", "X"),
        make_anchored_key("Y", "Y")
    ));
    
    engine.add_fact(HashableStatement::Gt(
        make_anchored_key("Y", "Y"),
        make_anchored_key("Z", "Z")
    ));
    
    engine.add_fact(HashableStatement::Equal(
        make_anchored_key("Z", "Z"),
        make_anchored_key("W", "W")
    ));

    // Add an irrelevant fact
    engine.add_fact(HashableStatement::ValueOf(
        make_anchored_key("A", "A"),
        HashableValue::String("Hello".to_string())
    ));

    // Set what we want to prove
    engine.set_target(HashableStatement::NotEqual(
        make_anchored_key("Y", "Y"),
        make_anchored_key("Z", "Z")
    ));

    // Try to prove it
    let proofs = engine.prove();
    
    if !proofs.is_empty() {
        println!("We can prove the target statement!");
        for (statement, chain) in proofs {
            engine.print_proof(statement, chain);
        }
    } else {
        println!("Cannot prove the target statement");
    }
}
