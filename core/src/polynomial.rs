use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Term {
    pub coeff: i32,
    pub exp: u32,
}

impl Term {
    pub fn new(coeff: i32, exp: u32) -> Self {
        Self { coeff, exp }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Polynomial {
    coeffs: Vec<i32>,
}

impl Polynomial {
    pub fn new() -> Self {
        Self { coeffs: Vec::new() }
    }

    pub fn from_term(term: Term) -> Self {
        let mut poly = Self::new();
        poly.set_coeff(term.exp, term.coeff);
        poly
    }

    pub fn from_terms(terms: &[Term]) -> Self {
        let mut poly = Self::new();
        for term in terms {
            let current = poly.get_coeff(term.exp);
            poly.set_coeff(term.exp, current + term.coeff);
        }
        poly
    }

    fn ensure_size(&mut self, exp: u32) {
        let needed = (exp + 1) as usize;
        if self.coeffs.len() < needed {
            self.coeffs.resize(needed, 0);
        }
    }

    pub fn get_coeff(&self, exp: u32) -> i32 {
        self.coeffs.get(exp as usize).copied().unwrap_or(0)
    }

    pub fn set_coeff(&mut self, exp: u32, coeff: i32) {
        self.ensure_size(exp);
        self.coeffs[exp as usize] = coeff;
    }

    pub fn add(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result = Polynomial { coeffs: vec![0; max_len] };
        for (i, &c) in self.coeffs.iter().enumerate() {
            result.coeffs[i] += c;
        }
        for (i, &c) in other.coeffs.iter().enumerate() {
            result.coeffs[i] += c;
        }
        result.normalize()
    }

    pub fn sub(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result = Polynomial { coeffs: vec![0; max_len] };
        for (i, &c) in self.coeffs.iter().enumerate() {
            result.coeffs[i] += c;
        }
        for (i, &c) in other.coeffs.iter().enumerate() {
            result.coeffs[i] -= c;
        }
        result.normalize()
    }

    pub fn mul_term(&self, coeff: i32, exp: u32) -> Polynomial {
        if coeff == 0 {
            return Polynomial::new();
        }
        let new_len = self.coeffs.len() + exp as usize;
        let mut result = Polynomial { coeffs: vec![0; new_len] };
        for (i, &c) in self.coeffs.iter().enumerate() {
            result.coeffs[i + exp as usize] = c * coeff;
        }
        result.normalize()
    }

    pub fn mul(&self, other: &Polynomial) -> Polynomial {
        if self.is_zero() || other.is_zero() {
            return Polynomial::new();
        }
        let new_len = self.coeffs.len() + other.coeffs.len() - 1;
        let mut result = Polynomial { coeffs: vec![0; new_len] };
        for (i, &a) in self.coeffs.iter().enumerate() {
            for (j, &b) in other.coeffs.iter().enumerate() {
                result.coeffs[i + j] += a * b;
            }
        }
        result.normalize()
    }

    fn normalize(mut self) -> Self {
        while self.coeffs.last() == Some(&0) {
            self.coeffs.pop();
        }
        self
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.iter().all(|&c| c == 0)
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.coeffs
            .iter()
            .enumerate()
            .rev() // Iterate from last element (highest exp) to first
            .filter(|(_, &c)| c != 0)
            .map(|(exp, &coeff)| Term::new(coeff, exp as u32))
            .collect()
    }

    pub fn quadratic_coeffs(&self) -> (i32, i32, i32) {
        (
            self.get_coeff(2),
            self.get_coeff(1),
            self.get_coeff(0),
        )
    }

    pub fn positive_terms(&self) -> Vec<Term> {
        self.to_terms().into_iter().filter(|t| t.coeff > 0).collect()
    }

    pub fn negative_terms(&self) -> Vec<Term> {
        self.to_terms().into_iter().filter(|t| t.coeff < 0).collect()
    }

    pub fn negate(&self) -> Polynomial {
        Polynomial {
            coeffs: self.coeffs.iter().map(|&c| -c).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polynomial_add() {
        let p1 = Polynomial::from_terms(&[Term::new(1, 2), Term::new(2, 1)]);
        let p2 = Polynomial::from_terms(&[Term::new(3, 1), Term::new(4, 0)]);
        let sum = p1.add(&p2);
        assert_eq!(sum.quadratic_coeffs(), (1, 5, 4));
    }

    #[test]
    fn test_polynomial_sub() {
        let p1 = Polynomial::from_terms(&[Term::new(1, 2), Term::new(5, 1)]);
        let p2 = Polynomial::from_terms(&[Term::new(2, 1), Term::new(3, 0)]);
        let diff = p1.sub(&p2);
        assert_eq!(diff.quadratic_coeffs(), (1, 3, -3));
    }

    #[test]
    fn test_polynomial_mul() {
        let p1 = Polynomial::from_terms(&[Term::new(1, 1), Term::new(2, 0)]);
        let p2 = Polynomial::from_terms(&[Term::new(1, 1), Term::new(3, 0)]);
        let prod = p1.mul(&p2);
        assert_eq!(prod.quadratic_coeffs(), (1, 5, 6));
    }
}
