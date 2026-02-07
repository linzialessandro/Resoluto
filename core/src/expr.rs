use crate::polynomial::{Polynomial, Term};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Term(Term),
    Sum(Vec<Expr>),
    SquareOfBinomial { a: i32, b: i32 },
    DifferenceOfSquares { a: i32, b: i32 },
    ProductOfBinomials { a: i32, b: i32, c: i32, d: i32 },
    MonomialMul { coeff: i32, exp: u32, inner: Box<Expr> },
    Fraction { num: Box<Expr>, den: Box<Expr> },
    Sqrt(Box<Expr>),
    Abs(Box<Expr>),
}

pub trait Expandable {
    fn expand(&self) -> Polynomial;
}

pub trait Renderable {
    fn to_latex(&self) -> String;
}

impl Expandable for Expr {
    fn expand(&self) -> Polynomial {
        match self {
            Expr::Term(t) => Polynomial::from_term(*t),

            Expr::Sum(exprs) => {
                exprs.iter().fold(Polynomial::new(), |acc, e| acc.add(&e.expand()))
            }

            Expr::SquareOfBinomial { a, b } => {
                let a2 = a * a;
                let ab2 = 2 * a * b;
                let b2 = b * b;
                Polynomial::from_terms(&[
                    Term::new(a2, 2),
                    Term::new(ab2, 1),
                    Term::new(b2, 0),
                ])
            }

            Expr::DifferenceOfSquares { a, b } => {
                let a2 = a * a;
                let b2 = b * b;
                Polynomial::from_terms(&[
                    Term::new(a2, 2),
                    Term::new(-b2, 0),
                ])
            }

            Expr::ProductOfBinomials { a, b, c, d } => {
                let ac = a * c;
                let ad_bc = a * d + b * c;
                let bd = b * d;
                Polynomial::from_terms(&[
                    Term::new(ac, 2),
                    Term::new(ad_bc, 1),
                    Term::new(bd, 0),
                ])
            }

            Expr::MonomialMul { coeff, exp, inner } => {
                inner.expand().mul_term(*coeff, *exp)
            }

            // For now, these new variants expand to empty polynomials or simple terms if possible,
            // but their main use is for structured display of rational/irrational equations.
            // Expansion logic for these is complex and might not be needed for the generation strategies
            // which build the final equation directly.
            // We'll return a zero polynomial by default or implement partial expansion if needed later.
            Expr::Fraction { .. } | Expr::Sqrt(_) | Expr::Abs(_) => Polynomial::new(),
        }
    }
}

impl Renderable for Expr {
    fn to_latex(&self) -> String {
        match self {
            Expr::Term(t) => format_term(t.coeff, t.exp, true),

            Expr::Sum(exprs) => {
                let non_zero_exprs: Vec<&Expr> = exprs.iter()
                    .filter(|e| match e {
                        Expr::Term(t) if t.coeff == 0 => false,
                        _ => true,
                    })
                    .collect();

                if non_zero_exprs.is_empty() {
                    return "0".to_string();
                }

                let mut result = String::new();
                for (i, expr) in non_zero_exprs.iter().enumerate() {
                    let latex = expr.to_latex();
                    if i == 0 {
                        result.push_str(&latex);
                    } else if latex.starts_with('-') {
                        result.push_str(" ");
                        result.push_str(&latex);
                    } else {
                        result.push_str(" + ");
                        result.push_str(&latex);
                    }
                }
                result
            }

            Expr::SquareOfBinomial { a, b } => {
                let inner = format_binomial(*a, *b);
                format!("\\left({}\\right)^2", inner)
            }

            Expr::DifferenceOfSquares { a, b } => {
                let left = format_binomial(*a, *b);
                let right = format_binomial(*a, -b);
                format!("\\left({}\\right)\\left({}\\right)", left, right)
            }

            Expr::ProductOfBinomials { a, b, c, d } => {
                let left = format_binomial(*a, *b);
                let right = format_binomial(*c, *d);
                format!("\\left({}\\right)\\left({}\\right)", left, right)
            }

            Expr::MonomialMul { coeff, exp, inner } => {
                if *coeff == -1 && *exp == 0 {
                    format!("-\\left({}\\right)", inner.to_latex())
                } else {
                    let monomial = format_monomial(*coeff, *exp);
                    format!("{}\\left({}\\right)", monomial, inner.to_latex())
                }
            }

            Expr::Fraction { num, den } => {
                format!("\\dfrac{{{}}}{{{}}}", num.to_latex(), den.to_latex())
            }

            Expr::Sqrt(inner) => {
                format!("\\sqrt{{{}}}", inner.to_latex())
            }

            Expr::Abs(inner) => {
                format!("\\left|{}\\right|", inner.to_latex())
            }
        }
    }
}

fn format_binomial(a: i32, b: i32) -> String {
    let x_part = match a {
        0 => String::new(),
        1 => "x".to_string(),
        -1 => "-x".to_string(),
        n => format!("{}x", n),
    };

    let const_part = match b {
        0 => String::new(),
        n if n > 0 && a != 0 => format!(" + {}", n),
        n if n < 0 && a != 0 => format!(" - {}", -n),
        n => format!("{}", n),
    };

    format!("{}{}", x_part, const_part)
}

fn format_monomial(coeff: i32, exp: u32) -> String {
    match (coeff, exp) {
        (0, _) => "0".to_string(),
        (1, 0) => "1".to_string(),
        (1, 1) => "x".to_string(),
        (1, e) => format!("x^{}", e),
        (-1, 0) => "-1".to_string(),
        (-1, 1) => "-x".to_string(),
        (-1, e) => format!("-x^{}", e),
        (c, 0) => format!("{}", c),
        (c, 1) => format!("{}x", c),
        (c, e) => format!("{}x^{}", c, e),
    }
}

fn format_term(coeff: i32, exp: u32, is_first: bool) -> String {
    if coeff == 0 {
        return if is_first { "0".to_string() } else { String::new() };
    }

    let sign = if coeff < 0 {
        if is_first { "-" } else { "- " }
    } else {
        if is_first { "" } else { "+ " }
    };

    let abs_coeff = coeff.abs();

    match exp {
        0 => format!("{}{}", sign, abs_coeff),
        1 if abs_coeff == 1 => format!("{}x", sign),
        1 => format!("{}{}x", sign, abs_coeff),
        e if abs_coeff == 1 => format!("{}x^{}", sign, e),
        e => format!("{}{}x^{}", sign, abs_coeff, e),
    }
}

pub fn terms_to_expr(terms: Vec<Term>) -> Expr {
    if terms.is_empty() {
        Expr::Term(Term::new(0, 0))
    } else if terms.len() == 1 {
        Expr::Term(terms[0])
    } else {
        Expr::Sum(terms.into_iter().map(Expr::Term).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_square_of_binomial_expand() {
        let expr = Expr::SquareOfBinomial { a: 1, b: 3 };
        let poly = expr.expand();
        assert_eq!(poly.quadratic_coeffs(), (1, 6, 9));
    }

    #[test]
    fn test_square_of_binomial_latex() {
        let expr = Expr::SquareOfBinomial { a: 1, b: 3 };
        assert_eq!(expr.to_latex(), "\\left(x + 3\\right)^2");
    }

    #[test]
    fn test_square_of_binomial_negative() {
        let expr = Expr::SquareOfBinomial { a: 2, b: -1 };
        let poly = expr.expand();
        assert_eq!(poly.quadratic_coeffs(), (4, -4, 1));
        assert_eq!(expr.to_latex(), "\\left(2x - 1\\right)^2");
    }

    #[test]
    fn test_difference_of_squares_expand() {
        let expr = Expr::DifferenceOfSquares { a: 1, b: 2 };
        let poly = expr.expand();
        assert_eq!(poly.quadratic_coeffs(), (1, 0, -4));
    }

    #[test]
    fn test_difference_of_squares_latex() {
        let expr = Expr::DifferenceOfSquares { a: 1, b: 2 };
        assert_eq!(expr.to_latex(), "\\left(x + 2\\right)\\left(x - 2\\right)");
    }

    #[test]
    fn test_product_of_binomials_expand() {
        let expr = Expr::ProductOfBinomials { a: 1, b: 2, c: 1, d: 3 };
        let poly = expr.expand();
        assert_eq!(poly.quadratic_coeffs(), (1, 5, 6));
    }

    #[test]
    fn test_product_of_binomials_latex() {
        let expr = Expr::ProductOfBinomials { a: 1, b: 2, c: 1, d: 3 };
        assert_eq!(expr.to_latex(), "\\left(x + 2\\right)\\left(x + 3\\right)");
    }

    #[test]
    fn test_monomial_mul_expand() {
        let inner = Expr::Sum(vec![
            Expr::Term(Term::new(1, 1)),
            Expr::Term(Term::new(2, 0)),
        ]);
        let expr = Expr::MonomialMul { coeff: 3, exp: 1, inner: Box::new(inner) };
        let poly = expr.expand();
        assert_eq!(poly.get_coeff(2), 3);
        assert_eq!(poly.get_coeff(1), 6);
    }

    #[test]
    fn test_sum_latex() {
        let expr = Expr::Sum(vec![
            Expr::SquareOfBinomial { a: 1, b: 2 },
            Expr::Term(Term::new(5, 0)),
        ]);
        assert_eq!(expr.to_latex(), "\\left(x + 2\\right)^2 + 5");
    }
}
