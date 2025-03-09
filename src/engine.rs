use ascent::ascent;
use pod2::frontend::{AnchoredKey, Value};
use pod2::middleware::NativeOperation;

use crate::types::*;

pub struct DeductionEngine {
    prog: AscentProgram,
}

impl DeductionEngine {
    pub fn new() -> Self {
        Self {
            prog: AscentProgram::default()
        }
    }


    pub fn add_fact(&mut self, fact: HashableStatement) {
        self.prog.known_statement.push((fact,));
    }

    pub fn set_target(&mut self, target: HashableStatement) {
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
    // Basic facts and helper relations
    relation known_statement(HashableStatement);
    relation target_statement(HashableStatement);
    relation can_prove(HashableStatement, DeductionChain);
    relation known_value(AnchoredKey, HashableValue);
    relation known_equal(AnchoredKey, AnchoredKey);
    relation known_gt(AnchoredKey, AnchoredKey);
    relation known_lt(AnchoredKey, AnchoredKey);
    
    // Relations for goal-directed proof search
    relation need_to_prove(HashableStatement);
    relation need_equal(AnchoredKey, AnchoredKey);
    relation need_gt(AnchoredKey, AnchoredKey);
    relation need_lt(AnchoredKey, AnchoredKey);
    relation need_not_equal(AnchoredKey, AnchoredKey);
    
    // Extract relationships from known statements
    known_value(ak, v) <--
        known_statement(stmt),
        if let HashableStatement::ValueOf(ak, v) = stmt;
    
    known_equal(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Equal(ak1, ak2) = stmt;

    known_gt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Gt(ak1, ak2) = stmt;

    known_lt(ak1, ak2) <--
        known_statement(stmt),
        if let HashableStatement::Lt(ak1, ak2) = stmt;

    // Set up what we need to prove from target statements
    need_to_prove(stmt) <--
        target_statement(stmt);

    need_gt(x, z) <--
        need_to_prove(stmt),
        if let HashableStatement::Gt(x, z) = stmt;

    need_lt(x, z) <--
        need_to_prove(stmt),
        if let HashableStatement::Lt(x, z) = stmt;

    need_equal(x, z) <--
        need_to_prove(stmt),
        if let HashableStatement::Equal(x, z) = stmt;

    need_not_equal(x, y) <--
        need_to_prove(stmt),
        if let HashableStatement::NotEqual(x, y) = stmt;

    // Base case: if we need to prove something and it's known, we can prove it
    can_prove(stmt, chain) <--
        need_to_prove(stmt),
        known_statement(stmt),
        let chain = vec![];

    // Rule 1: If we need to prove X = Y and Y = Z then X = Z
    can_prove(new_stmt, new_chain) <--
        need_equal(x, z),
        known_equal(x, y),
        known_equal(y, z),
        let new_stmt = HashableStatement::Equal(x.clone(), z.clone()),
        let new_chain = vec![(
            NativeOperation::TransitiveEqualFromStatements as u8,
            vec![
                HashableStatement::Equal(x.clone(), y.clone()),
                HashableStatement::Equal(y.clone(), z.clone())
            ],
            new_stmt.clone()
        )];

    // Rule 2: If we need to prove X ≠ Y and X > Y then X ≠ Y
    can_prove(new_stmt, new_chain) <--
        need_not_equal(x, y),
        known_gt(x, y),
        let new_stmt = HashableStatement::NotEqual(x.clone(), y.clone()),
        let new_chain = vec![(
            NativeOperation::GtToNotEqual as u8,
            vec![HashableStatement::Gt(x.clone(), y.clone())],
            new_stmt.clone()
        )];

    // Rule 3: If we need to prove X ≠ Y and X < Y then X ≠ Y
    can_prove(new_stmt, new_chain) <--
        need_not_equal(x, y),
        known_lt(x, y),
        let new_stmt = HashableStatement::NotEqual(x.clone(), y.clone()),
        let new_chain = vec![(
            NativeOperation::LtToNotEqual as u8,
            vec![HashableStatement::Lt(x.clone(), y.clone())],
            new_stmt.clone()
        )];

    // Note: We do NOT implement transitive GT/LT because POD2 doesn't support it yet
    // The only way to get GT/LT statements is through EntryGt/EntryLt comparing actual values
} 