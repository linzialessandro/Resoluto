use crate::expr::Expr;
use crate::polynomial::{Polynomial, Term};
use crate::random_range;

#[derive(Debug, Clone, PartialEq)]
pub struct ObfuscatedEquation {
    pub lhs: Expr,
    pub rhs: Expr,
}

pub fn obfuscate(target_poly: &Polynomial, difficulty: &crate::Difficulty) -> ObfuscatedEquation {
    let (mut lhs_base, mut rhs_base) = match difficulty {
        crate::Difficulty::Easy => (
            generate_random_structure_easy(),
            generate_random_structure_easy(),
        ),
        crate::Difficulty::Medium => (
            generate_random_structure_medium(),
            generate_random_structure_medium(),
        ),
        crate::Difficulty::Hard => (
            generate_random_structure_hard(),
            generate_random_structure_hard(),
        ),
    };

    if matches!(difficulty, crate::Difficulty::Medium | crate::Difficulty::Hard) {
        let redundant_terms = generate_redundant_poly(difficulty);
        lhs_base = combine_expr(lhs_base, redundant_terms.clone());
        rhs_base = combine_expr(rhs_base, redundant_terms);
    }

    use crate::expr::Expandable;
    let p_lhs = lhs_base.expand();
    let p_rhs = rhs_base.expand();

    let remainder = target_poly.sub(&p_lhs).add(&p_rhs);

    let positive_terms = remainder.positive_terms();
    let negative_terms = remainder.negate().positive_terms(); // Get -R terms as positive

    let lhs_final = combine_expr(lhs_base, positive_terms);
    let rhs_final = combine_expr(rhs_base, negative_terms);

    ObfuscatedEquation {
        lhs: lhs_final,
        rhs: rhs_final,
    }
}

fn generate_redundant_poly(difficulty: &crate::Difficulty) -> Vec<Term> {
    let mut terms = Vec::new();
    let count = match difficulty {
        crate::Difficulty::Hard => random_range(1, 3), // 1 or 2 terms
        _ => 1,
    };
    
    for _ in 0..count {
        let power = random_range(0, 2); // 0 or 1 (constant or linear)
        let coeff = loop {
             let v = random_range(-8, 8); 
             if v != 0 { break v; }
        };
        terms.push(Term::new(coeff, power as u32));
    }
    terms
}

fn combine_expr(base: Expr, extra_terms: Vec<Term>) -> Expr {
    if extra_terms.is_empty() {
        return base;
    }
    
    let extra_expr = if extra_terms.len() == 1 {
        Expr::Term(extra_terms[0])
    } else {
        Expr::Sum(extra_terms.into_iter().map(Expr::Term).collect())
    };

    match base {
        Expr::Sum(mut exprs) => {
            exprs.push(extra_expr);
            Expr::Sum(exprs)
        }
        _ => Expr::Sum(vec![base, extra_expr]),
    }
}


fn generate_random_structure_easy() -> Expr {
    let choice = random_range(0, 2);
    match choice {
        0 => {
             let a = loop {
                 let val = random_range(-5, 5);
                 if val != 0 { break val; }
             };
             Expr::Term(Term::new(a, 1))
        }
        1 => {
             let c = loop {
                 let val = random_range(-10, 10);
                 if val != 0 { break val; }
             };
             Expr::Term(Term::new(c, 0))
        }
        _ => Expr::Term(Term::new(0, 0)),
    }
}

fn generate_random_structure_medium() -> Expr {
    let choice = random_range(0, 3);
    match choice {
        0 => {
            let a = if random_range(0, 1) == 0 { 1 } else { -1 };
            let b = loop {
                let val = random_range(-5, 5);
                if val != 0 { break val; }
            };
            Expr::SquareOfBinomial { a, b }
        }
        1 => {
            let a = 1;
            let b = random_range(1, 5);
            Expr::DifferenceOfSquares { a, b }
        }
        2 => {
            let k = random_range(2, 4);
            let a = if random_range(0, 1) == 0 { 1 } else { -1 };
            let b = random_range(-4, 4);
            let inner = Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0)),
            ]);
            Expr::MonomialMul {
                coeff: k,
                exp: 0,
                inner: Box::new(inner),
            }
        }
        _ => generate_random_structure_easy(),
    }
}

fn generate_random_structure_hard() -> Expr {
    let choice = random_range(0, 3);
    match choice {
        0 => {
            let a = random_range(2, 4) * (if random_range(0, 1) == 0 { 1 } else { -1 });
            let b = loop {
                let val = random_range(-6, 6);
                if val != 0 { break val; }
            };
            Expr::SquareOfBinomial { a, b }
        }
        1 => {
            let a = loop { let v = random_range(-3, 3); if v != 0 { break v; } };
            let c = loop { let v = random_range(-3, 3); if v != 0 { break v; } };
            let b = random_range(-6, 6);
            let d = random_range(-6, 6);
            Expr::ProductOfBinomials { a, b, c, d }
        }
        2 => {
            let k = loop { let v = random_range(-3, 3); if v != 0 { break v; } };
            let a = loop { let v = random_range(-3, 3); if v != 0 { break v; } };
            let b = random_range(-5, 5);
            let inner = Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0)),
            ]);
            Expr::MonomialMul {
                coeff: k,
                exp: 1, // x^1
                inner: Box::new(inner),
            }
        }
        _ => generate_random_structure_medium(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expandable;

    #[test]
    fn test_combine_expr() {
        let base = Expr::Term(Term::new(1, 2)); // x^2
        let extra = vec![Term::new(2, 1), Term::new(3, 0)]; // 2x + 3
        let combined = combine_expr(base, extra);
        if let Expr::Sum(parts) = combined {
            assert_eq!(parts.len(), 2);
        } else {
            panic!("Expected Sum");
        }
    }

    #[test]
    fn test_obfuscation_balancing_logic() {
        let target = Polynomial::from_terms(&[
            Term::new(1, 2),
            Term::new(5, 1),
            Term::new(6, 0),
        ]);
        
        let lhs_base = Expr::SquareOfBinomial { a: 1, b: 2 }; // x^2 + 4x + 4
        let rhs_base = Expr::Term(Term::new(1, 0)); // 1
        
        let p_lhs = lhs_base.expand();
        let p_rhs = rhs_base.expand();
        let remainder = target.sub(&p_lhs).add(&p_rhs);
        
        let positive = remainder.positive_terms(); // x, 3
        let negative = remainder.negate().positive_terms(); // none
        
        let lhs_final = combine_expr(lhs_base.clone(), positive);
        let rhs_final = combine_expr(rhs_base.clone(), negative);
        
        let final_lhs_poly = lhs_final.expand();
        let final_rhs_poly = rhs_final.expand();
        let final_eq = final_lhs_poly.sub(&final_rhs_poly);
        
        assert_eq!(final_eq.quadratic_coeffs(), (1, 5, 6));
    }
}
