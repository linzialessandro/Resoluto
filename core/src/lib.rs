use serde::{Deserialize, Serialize};

pub mod expr;
pub mod polynomial;
mod obfuscate;

use expr::{Expr, Renderable};
use polynomial::{Polynomial, Term};
use obfuscate::obfuscate;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Difficulty {
    Easy,
    Medium,
    Hard,
}

impl Difficulty {
    pub fn as_str(&self) -> &'static str {
        match self {
            Difficulty::Easy => "easy",
            Difficulty::Medium => "medium",
            Difficulty::Hard => "hard",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Relation {
    Eq,
    Lt,
    Gt,
    Lte,
    Gte,
    Neq,
}

impl Relation {
    pub fn to_latex(&self) -> &'static str {
        match self {
            Relation::Eq => "=",
            Relation::Lt => "<",
            Relation::Gt => ">",
            Relation::Lte => "\\leq",
            Relation::Gte => "\\geq",
            Relation::Neq => "\\neq",
        }
    }

    pub fn flip(&self) -> Self {
        match self {
            Relation::Eq => Relation::Eq,
            Relation::Lt => Relation::Gt,
            Relation::Gt => Relation::Lt,
            Relation::Lte => Relation::Gte,
            Relation::Gte => Relation::Lte,
            Relation::Neq => Relation::Neq,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SolutionSet {
    Finite(f64, f64),           // x \in (a, b)
    External(f64, f64),         // x < a U x > b
    Ray(f64, Relation),         // x > a or x <= a
    Union(Vec<SolutionSet>),    // General union of sets
    Empty,                      // No solution
    AllReal,                    // All real numbers
    Set(Vec<f64>),             // Discrete set (old roots)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProblemType {
    Linear,
    Quadratic,
    Rational,
    Irrational,
    AbsoluteValue,
    LinearInequality,
    QuadraticInequality,
    RationalInequality,
    IrrationalInequality,
    AbsoluteValueInequality,
}

impl ProblemType {
    pub fn as_str(&self) -> &'static str {
        match self {
            ProblemType::Linear => "linear",
            ProblemType::Quadratic => "quadratic",
            ProblemType::Rational => "rational",
            ProblemType::Irrational => "irrational",
            ProblemType::AbsoluteValue => "absolute-value",
            ProblemType::LinearInequality => "linear-inequality",
            ProblemType::QuadraticInequality => "quadratic-inequality",
            ProblemType::RationalInequality => "rational-inequality",
            ProblemType::IrrationalInequality => "irrational-inequality",
            ProblemType::AbsoluteValueInequality => "absolute-value-inequality",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Problem {
    pub problem_type: ProblemType,
    pub difficulty: Difficulty,
    pub a: i32,
    pub b: i32,
    pub c: i32,
    pub roots: [f64; 2],
    pub root_count: usize,
    
    pub lhs_expr: Option<Expr>,
    pub rhs_expr: Option<Expr>,
    
    pub relation: Relation,
    pub solution_set: Option<SolutionSet>,
    
    pub explicit_solution: Option<String>,
    pub debug_info: String,
}

impl Problem {
    pub fn to_latex(&self) -> String {
        if let (Some(lhs), Some(rhs)) = (&self.lhs_expr, &self.rhs_expr) {
            format!("{} {} {}", lhs.to_latex(), self.relation.to_latex(), rhs.to_latex())
        } else {
            match self.problem_type {
                ProblemType::Linear => self.format_linear(),
                ProblemType::Quadratic => self.format_quadratic(),
                _ => String::from("Equation display not implemented for this type key"),
            }
        }
    }

    pub fn solution_latex(&self) -> String {
        if let Some(explicit) = &self.explicit_solution {
            return explicit.clone();
        }
        
        if let Some(sol_set) = &self.solution_set {
            return match sol_set {
                SolutionSet::Finite(a, b) => format!("x \\in ({}, {})", format_number(*a), format_number(*b)),
                SolutionSet::External(a, b) => format!("x \\in (-\\infty, {}) \\cup ({}, +\\infty)", format_number(*a), format_number(*b)),
                SolutionSet::Ray(a, rel) => {
                    match rel {
                        Relation::Lt => format!("x \\in (-\\infty, {})", format_number(*a)),
                        Relation::Lte => format!("x \\in (-\\infty, {}]", format_number(*a)),
                        Relation::Gt => format!("x \\in ({}, +\\infty)", format_number(*a)),
                        Relation::Gte => format!("x \\in [{}, +\\infty)", format_number(*a)),
                        _ => format!("x {} {}", rel.to_latex(), format_number(*a))
                    }
                },
                SolutionSet::Union(sets) => {
                     let intervals = sets.iter().map(|s| {
                         match s {
                            SolutionSet::Finite(a, b) => format!("({}, {})", format_number(*a), format_number(*b)),
                            SolutionSet::External(a, b) => format!("(-\\infty, {}) \\cup ({}, +\\infty)", format_number(*a), format_number(*b)),
                            SolutionSet::Ray(a, rel) => {
                                match rel {
                                    Relation::Lt => format!("(-\\infty, {})", format_number(*a)),
                                    Relation::Lte => format!("(-\\infty, {}]", format_number(*a)),
                                    Relation::Gt => format!("({}, +\\infty)", format_number(*a)),
                                    Relation::Gte => format!("[{}, +\\infty)", format_number(*a)),
                                    _ => format!("x {} {}", rel.to_latex(), format_number(*a))
                                }
                            },
                            _ => String::from("...") // Nested unions not fully supported for simple display yet
                         }
                     }).collect::<Vec<_>>().join(" \\cup ");
                     format!("x \\in {}", intervals)
                },
                SolutionSet::Empty => String::from("\\emptyset"),
                SolutionSet::AllReal => String::from("\\mathbb{R}"),
                SolutionSet::Set(vals) => vals.iter().map(|v| format!("x = {}", format_number(*v))).collect::<Vec<_>>().join(", "),
            };
        }
        
        if self.root_count == 1 {
            format!("x = {}", format_number(self.roots[0]))
        } else if self.root_count == 2 {
            let r1 = format_number(self.roots[0]);
            let r2 = format_number(self.roots[1]);
            if r1 == r2 {
                format!("x = {}", r1)
            } else {
                format!("x_1 = {}, \\quad x_2 = {}", r1, r2)
            }
        } else {
            String::from("impossible")
        }
    }

    fn format_linear(&self) -> String {
        let mut parts = Vec::new();
        
        if self.a != 0 {
            parts.push(format_coefficient(self.a, "x", true));
        }
        
        if self.b != 0 {
            parts.push(format_constant(self.b, parts.is_empty()));
        }
        
        if parts.is_empty() {
            return String::from("0 = 0");
        }
        
        format!("{} = 0", parts.join(" "))
    }

    fn format_quadratic(&self) -> String {
        let mut parts = Vec::new();
        
        if self.a != 0 {
            parts.push(format_coefficient(self.a, "x^2", true));
        }
        
        if self.b != 0 {
            parts.push(format_coefficient(self.b, "x", parts.is_empty()));
        }
        
        if self.c != 0 {
            parts.push(format_constant(self.c, parts.is_empty()));
        }
        
        if parts.is_empty() {
            return String::from("0 = 0");
        }
        
        format!("{} = 0", parts.join(" "))
    }
}

fn format_coefficient(coef: i32, var: &str, is_first: bool) -> String {
    match coef {
        0 => String::new(),
        1 => {
            if is_first {
                var.to_string()
            } else {
                format!("+ {}", var)
            }
        }
        -1 => {
            if is_first {
                format!("-{}", var)
            } else {
                format!("- {}", var)
            }
        }
        n if n > 0 => {
            if is_first {
                format!("{}{}", n, var)
            } else {
                format!("+ {}{}", n, var)
            }
        }
        n => {
            if is_first {
                format!("{}{}", n, var)
            } else {
                format!("- {}{}", -n, var)
            }
        }
    }
}

fn format_constant(c: i32, is_first: bool) -> String {
    match c {
        0 => String::new(),
        n if n > 0 => {
            if is_first {
                format!("{}", n)
            } else {
                format!("+ {}", n)
            }
        }
        n => {
            if is_first {
                format!("{}", n)
            } else {
                format!("- {}", -n)
            }
        }
    }
}


fn format_number(n: f64) -> String {
    if n.fract().abs() < 1e-9 {
        format!("{}", n as i32)
    } else {
        for den in 2..=100 {
            let num = (n * den as f64).round();
            if (n * den as f64 - num).abs() < 1e-9 {
                return format!("\\frac{{{}}}{{{}}}", num as i32, den);
            }
        }
        format!("{:.2}", n)
    }
}

pub fn generate_problem(
    problem_type: ProblemType,
    difficulty: Difficulty,
) -> Problem {
    match problem_type {
        ProblemType::Linear => generate_linear(difficulty),
        ProblemType::Quadratic => generate_quadratic(difficulty),
        ProblemType::Rational => generate_rational(difficulty),
        ProblemType::Irrational => generate_irrational(difficulty),
        ProblemType::AbsoluteValue => generate_absolute(difficulty),
        ProblemType::LinearInequality => generate_linear_inequality(difficulty),
        ProblemType::QuadraticInequality => generate_quadratic_inequality(difficulty),
        ProblemType::RationalInequality => generate_rational_inequality(difficulty),
        ProblemType::IrrationalInequality => generate_irrational_inequality(difficulty),
        ProblemType::AbsoluteValueInequality => generate_absolute_inequality(difficulty),
    }
}

fn generate_linear_inequality(difficulty: Difficulty) -> Problem {
    let mut prob = generate_linear(difficulty);
    prob.problem_type = ProblemType::LinearInequality;
    
    let rel = match random_range(0, 3) {
        0 => Relation::Gt,
        1 => Relation::Lt,
        2 => Relation::Gte,
        _ => Relation::Lte,
    };
    
    let m = prob.a;
    let r = prob.roots[0];
    
    let sol_is_gt = random_range(0, 1) == 0;
    let is_strict = matches!(rel, Relation::Gt | Relation::Lt);
    
    let sol_rel = if sol_is_gt {
        if is_strict { Relation::Gt } else { Relation::Gte }
    } else {
        if is_strict { Relation::Lt } else { Relation::Lte }
    };
    
    let prob_rel = if m > 0 {
        sol_rel
    } else {
        sol_rel.flip()
    };
    
    prob.relation = prob_rel;
    prob.solution_set = Some(SolutionSet::Ray(r, sol_rel));
    prob.explicit_solution = None;
    
    prob
}

fn generate_quadratic_inequality(difficulty: Difficulty) -> Problem {
    let mut prob = generate_quadratic(difficulty);
    prob.problem_type = ProblemType::QuadraticInequality;
    
    let r1 = prob.roots[0];
    let r2 = prob.roots[1];
    let (min, max) = if r1 < r2 { (r1, r2) } else { (r2, r1) };
    
    let internal = random_range(0, 1) == 0;
    let strict = random_range(0, 1) == 0;
    
    let a = prob.a;
    let opens_up = a > 0;
    
    let (prob_rel, sol_set) = if internal {
        let rel = if opens_up {
            if strict { Relation::Lt } else { Relation::Lte }
        } else {
            if strict { Relation::Gt } else { Relation::Gte }
        };
        
        if strict {
            (rel, SolutionSet::Finite(min, max))
        } else {
            (Relation::Lt, SolutionSet::Finite(min, max))
        }
    } else {
        let rel = if opens_up {
            if strict { Relation::Gt } else { Relation::Gte }
        } else {
            if strict { Relation::Lt } else { Relation::Lte }
        };
        
        if strict {
            (rel, SolutionSet::External(min, max))
        } else {
            (Relation::Gt, SolutionSet::External(min, max))
        }
    };
    
    let final_rel = if strict { prob_rel } else {
        match prob_rel {
            Relation::Lte => Relation::Lt,
            Relation::Gte => Relation::Gt,
            _ => prob_rel
        }
    };
    
    // Check if the underlying quadratic came with a symbolic solution (surds)
    // and if so, construct a symbolic solution for the inequality.
    let explicit_sol = if let Some(base_str) = &prob.explicit_solution {
        if base_str.starts_with("x = ") && base_str.contains("\\pm \\sqrt{") {
            let parts: Vec<&str> = base_str.split("\\pm \\sqrt{").collect();
            if parts.len() == 2 {
                let p_str = parts[0].trim_start_matches("x = ").trim();
                let q_str = parts[1].trim_end_matches('}');
                
                let sqrt_part = format!("\\sqrt{{{}}}", q_str);
                
                let min_s = if p_str == "0" {
                    format!("-{}", sqrt_part)
                } else {
                    format!("{} - {}", p_str, sqrt_part)
                };
                
                let max_s = if p_str == "0" {
                    sqrt_part
                } else {
                    format!("{} + {}", p_str, sqrt_part)
                };

                let (opener, closer) = match final_rel {
                    Relation::Lte | Relation::Gte => ('[', ']'),
                    _ => ('(', ')'),
                };

                match &sol_set {
                    SolutionSet::Finite(..) => {
                        Some(format!("x \\in {}{}, {}{}", opener, min_s, max_s, closer))
                    },
                    SolutionSet::External(..) => {
                         // External: (-inf, min) U (max, +inf)
                         // The bracket on min/max generally follows the relation inclusive/exclusive logic
                         // But for External, if problem is ">", result is x < min OR x > max.
                         // Strict > means strict < and > in solution.
                         // Non-strict >= means <= and >= in solution.
                         Some(format!("x \\in (-\\infty, {}{} \\cup {}{}, +\\infty)", min_s, closer, opener, max_s))
                    },
                     _ => None
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    prob.relation = final_rel;
    prob.solution_set = Some(sol_set);
    prob.explicit_solution = explicit_sol;
    
    prob
}

fn generate_rational_inequality(difficulty: Difficulty) -> Problem {
    // Generate P(x)/Q(x).
    // Analyze sign changes at roots and poles.
    // For simplicity, reuse rational equation generator, get LHS - RHS,
    // and analyze the resulting rational function sign.
    // This is complex because generate_rational often results in P/Q = K.
    // We can move K to LHS: P/Q - K.
    
    // Simpler strategy:
    // Generate (x-r1)/(x-r2) > 0 or < 0.
    // Or (x-r1)(x-r2)/(x-r3) ...
    
    // Let's implement a specific generator for inequalities rather than reusing equation gen
    // to ensure cleaner sign analysis.
    
    loop {
        // Structure: (x - a) / (x - b) REL 0
        // Difficulty Easy/Medium.
        // Hard: (x-a)(x-b)/(x-c)
        
        let r1 = random_range(-5, 5);
        let r2 = random_range(-5, 5);
        if r1 == r2 { continue; }
        
        let num = Expr::Sum(vec![
            Expr::Term(Term::new(1, 1)),
            Expr::Term(Term::new(-r1, 0))
        ]);
        let den = Expr::Sum(vec![
            Expr::Term(Term::new(1, 1)),
            Expr::Term(Term::new(-r2, 0))
        ]);
        
        // Form: (x - r1) / (x - r2) > 0
        // Critical points: r1, r2.
        // Sign changes at each.
        // If r1 < r2:
        //    x < r1: (-)/(-) = +
        //    r1 < x < r2: (+)/(-) = -
        //    x > r2: (+)/(+) = +
        
        let (min, max) = if r1 < r2 { (r1, r2) } else { (r2, r1) };
        let is_positive_req = random_range(0, 1) == 0; // > 0
        
        let sol = if is_positive_req {
            SolutionSet::External(min as f64, max as f64)
        } else {
            SolutionSet::Finite(min as f64, max as f64)
        };
        
        let rel = if is_positive_req { Relation::Gt } else { Relation::Lt };
        
        let lhs = Expr::Fraction {
            num: Box::new(num),
            den: Box::new(den),
        };
        
        let rhs = Expr::Term(Term::new(0, 0));
        
        return Problem {
            problem_type: ProblemType::RationalInequality,
            difficulty,
            a: 0, b: 0, c: 0,
            roots: [r1 as f64, r2 as f64],
            root_count: 2,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Rational Ineq. r1={}, r2={}", r1, r2),
        };
    }
}

fn generate_irrational_inequality(difficulty: Difficulty) -> Problem {
    let template = match difficulty {
        Difficulty::Easy => if random_range(0, 2) == 0 { 0 } else { 1 },
        Difficulty::Medium => random_range(2, 4),
        Difficulty::Hard => random_range(4, 7),
    };

    match template {
        6 => generate_irrational_inequality_double(difficulty),
        5 => generate_irrational_inequality_advanced_isolation(difficulty),
        4 => generate_irrational_inequality_two_radicals(difficulty),
        3 => generate_irrational_inequality_linear_rhs(difficulty),
        2 => generate_irrational_inequality_displaced(difficulty),
        1 => generate_irrational_inequality_simple(difficulty),
        _ => generate_irrational_inequality_basic(difficulty),
    }
}

fn generate_irrational_inequality_basic(difficulty: Difficulty) -> Problem {
    let r = random_range(-5, 5);
    let k = random_range(1, 5);
    let is_lt = random_range(0, 1) == 0;
    
    let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
        Expr::Term(Term::new(1, 1)),
        Expr::Term(Term::new(-r, 0))
    ])));
    let rhs = Expr::Term(Term::new(k, 0));
    
    let sol = if is_lt {
        SolutionSet::Finite(r as f64, (r + k*k) as f64)
    } else {
        SolutionSet::Ray((r + k*k) as f64, Relation::Gt)
    };
    
    let rel = if is_lt { Relation::Lt } else { Relation::Gt };
    
    Problem {
        problem_type: ProblemType::IrrationalInequality,
        difficulty,
        a: 0, b: 0, c: 0,
        roots: [r as f64, 0.0],
        root_count: 1,
        lhs_expr: Some(lhs),
        rhs_expr: Some(rhs),
        relation: rel,
        solution_set: Some(sol),
        explicit_solution: None,
        debug_info: format!("Irr Ineq Basic. r={}, k={}", r, k),
    }
}

fn generate_irrational_inequality_simple(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let c = random_range(1, 10);
        let is_lt = random_range(0, 1) == 0;
        
        let a = loop { let v = random_range(1, 6); if v != 0 { break v; } };
        let val_sq = c * c;
        let b = val_sq - a * x;
        
        if b.abs() > 50 { continue; }
        if a * x + b < 0 { continue; }
        
        let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Term(Term::new(c, 0));
        
        let sol = if is_lt {
            let domain_start = (-b as f64) / (a as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
        };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            a: 0, b: 0, c: 0,
            roots: [x as f64, 0.0],
            root_count: 1,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Simple. x={}", x),
        };
    }
}

fn generate_irrational_inequality_displaced(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let c = random_range(1, 10);
        let is_lt = random_range(0, 1) == 0;
        
        let a = loop { let v = random_range(1, 6); if v != 0 { break v; } };
        let val_sq = c * c;
        let b = val_sq - a * x;
        
        if b.abs() > 50 { continue; }
        
        let k = random_range(-5, 5);
        let d = c + k;
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0))
            ]))),
            Expr::Term(Term::new(k, 0))
        ]);
        let rhs = Expr::Term(Term::new(d, 0));
        
        let sol = if is_lt {
            let domain_start = (-b as f64) / (a as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
       };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            a: 0, b: 0, c: 0,
            roots: [x as f64, 0.0],
            root_count: 1,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Displaced. x={}", x),
        };
    }
}

fn generate_irrational_inequality_linear_rhs(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let c = random_range(1, 4);
        let d = random_range(-10, 10);
        let is_lt = random_range(0, 1) == 0;
        
        let rhs_val = c * x + d;
        if rhs_val < 0 { continue; }
        
        let val_sq = rhs_val * rhs_val;
        
        let a = loop { let v = random_range(1, 6); if v != 0 { break v; } };
        let b = val_sq - a * x;
        
        if b.abs() > 100 { continue; }
        
        let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Sum(vec![
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ]);
        
        let sol = if is_lt {
            let domain_start = (-b as f64) / (a as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
        };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            a: 0, b:0, c:0,
            roots: [x as f64, 0.0],
            root_count: 1,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Linear RHS. x={}", x),
        };
    }
}

fn generate_irrational_inequality_two_radicals(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let val = random_range(0, 50);
        let is_lt = random_range(0, 1) == 0;
        
        let a = random_range(1, 5);
        let c = loop { let v = random_range(1, 5); if v != a { break v; } };
        
        let b = val - a * x;
        let d = val - c * x;
        
        if a * x + b < 0 || c * x + d < 0 { continue; }
        
        let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ])));
        
        let sol = if is_lt {
            let domain_start = ((-b) as f64 / a as f64).max((-d) as f64 / c as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
        };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Two Radicals. x={}", x),
        };
    }
}

fn generate_irrational_inequality_advanced_isolation(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-8, 8);
        let v = random_range(2, 7);
        let sq = v * v;
        let is_lt = random_range(0, 1) == 0;
        
        let a = random_range(1, 4);
        let b = sq - a * x;
        
        let c = random_range(1, 3);
        let d = random_range(-8, 8);
        let k = v - (c * x + d);
        
        if b.abs() > 60 || k.abs() > 15 { continue; }
        if c * x + d < 0 { continue; }
        if a * x + b < 0 { continue; }
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0))
            ]))),
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ]);
        let rhs = Expr::Term(Term::new(v, 0));
        
        let sol = if is_lt {
            let domain_start = (-b as f64) / (a as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
        };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Adv Isolation. x={}", x),
        };
    }
}

fn generate_irrational_inequality_double(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let v1 = random_range(1, 8);
        let v2 = random_range(1, 8);
        let e = v1 + v2;
        let is_lt = random_range(0, 1) == 0;
        
        let sq1 = v1 * v1;
        let sq2 = v2 * v2;
        
        let a = loop { let v = random_range(1, 5); if v != 0 { break v; } };
        let b = sq1 - a * x;
        
        let c = loop { let v = random_range(1, 5); if v != 0 { break v; } };
        let d = sq2 - c * x;
        
        if a * x + b < 0 || c * x + d < 0 { continue; }
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0))
            ]))),
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(c, 1)),
                Expr::Term(Term::new(d, 0))
            ])))
        ]);
        let rhs = Expr::Term(Term::new(e, 0));
        
        let sol = if is_lt {
            let domain_start = ((-b) as f64 / a as f64).max((-d) as f64 / c as f64);
            SolutionSet::Finite(domain_start, x as f64)
        } else {
            SolutionSet::Ray(x as f64, Relation::Gt)
        };
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        
        return Problem {
            problem_type: ProblemType::IrrationalInequality,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Irr Ineq Double. x={}, v1={}, v2={}", x, v1, v2),
        };
    }
}

fn generate_absolute_inequality(difficulty: Difficulty) -> Problem {
    let template = match difficulty {
        Difficulty::Easy => 0,
        Difficulty::Medium => random_range(0, 3),
        Difficulty::Hard => random_range(1, 6),
    };

    match template {
        5 => generate_absolute_inequality_quadratic(difficulty),
        4 => generate_absolute_inequality_nested(difficulty),
        3 => generate_absolute_inequality_two_abs(difficulty),
        2 => generate_absolute_inequality_linear_rhs(difficulty),
        1 => generate_absolute_inequality_simple_complex(difficulty),
        _ => generate_absolute_inequality_basic(difficulty),
    }
}

fn generate_absolute_inequality_basic(difficulty: Difficulty) -> Problem {
    let a = random_range(-5, 5);
    let k = random_range(1, 6);
    let is_lt = random_range(0, 1) == 0;
    
    let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
        Expr::Term(Term::new(1, 1)),
        Expr::Term(Term::new(-a, 0))
    ])));
    let rhs = Expr::Term(Term::new(k, 0));
    
    let rel = if is_lt { Relation::Lt } else { Relation::Gt };
    
    let sol = if is_lt {
        SolutionSet::Finite((a - k) as f64, (a + k) as f64)
    } else {
        SolutionSet::External((a - k) as f64, (a + k) as f64)
    };
    
    Problem {
        problem_type: ProblemType::AbsoluteValueInequality,
        difficulty,
        a: 0, b:0, c:0,
        roots: [a as f64, 0.0],
        root_count: 1,
        lhs_expr: Some(lhs),
        rhs_expr: Some(rhs),
        relation: rel,
        solution_set: Some(sol),
        explicit_solution: None,
        debug_info: format!("Abs Ineq Basic. center={}, dist={}", a, k),
    }
}

fn generate_absolute_inequality_simple_complex(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-10, 10);
        let r2 = random_range(-10, 10);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 4);
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let c = (a * diff) / 2;
        let is_lt = random_range(0, 1) == 0;
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Term(Term::new(c, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        let sol = if is_lt {
            SolutionSet::Finite(roots[0], roots[1])
        } else {
            SolutionSet::External(roots[0], roots[1])
        };

        return Problem {
            problem_type: ProblemType::AbsoluteValueInequality,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Abs Ineq Simple. r={},{}", r1, r2),
        }
    }
}

fn generate_absolute_inequality_linear_rhs(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-8, 8);
        let r2 = random_range(-8, 8);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 5);
        let c = random_range(1, 5);
        if a == c { continue; }
        
        let two_d = a * (r1 - r2) - c * (r1 + r2);
        let two_b = -a * (r1 + r2) + c * (r1 - r2);
        
        if two_d % 2 != 0 || two_b % 2 != 0 { continue; }
        
        let d = two_d / 2;
        let b = two_b / 2;
        
        if c * r1 + d < 0 || c * r2 + d < 0 { continue; }
        
        let is_lt = random_range(0, 1) == 0;
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Sum(vec![
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ]);
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        let sol = if is_lt {
            SolutionSet::Finite(roots[0], roots[1])
        } else {
            SolutionSet::External(roots[0], roots[1])
        };

        return Problem {
            problem_type: ProblemType::AbsoluteValueInequality,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b:0, c:0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Abs Ineq Linear RHS. r={},{}", r1, r2),
        };
    }
}

fn generate_absolute_inequality_two_abs(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-8, 8);
        let r2 = random_range(-8, 8);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 5);
        let c = loop { let v = random_range(1, 5); if v != a { break v; } };
        
        let two_d = a * (r1 - r2) - c * (r1 + r2);
        let two_b = -a * (r1 + r2) + c * (r1 - r2);
        
        if two_d % 2 != 0 || two_b % 2 != 0 { continue; }
        
        let d = two_d / 2;
        let b = two_b / 2;
        let is_lt = random_range(0, 1) == 0;
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ])));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        let sol = if is_lt {
            SolutionSet::Finite(roots[0], roots[1])
        } else {
            SolutionSet::External(roots[0], roots[1])
        };

        return Problem {
            problem_type: ProblemType::AbsoluteValueInequality,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b:0, c:0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Abs Ineq Two Abs. r={},{}", r1, r2),
        };
    }
}

fn generate_absolute_inequality_nested(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-8, 8);
        let r2 = random_range(-8, 8);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 4);
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let k = (a * diff) / 2;
        
        let min_d = (k / 2) + 1;
        let d = random_range(min_d, min_d + 5);
        let c = k - d;
        
        if c == 0 { continue; }
        let is_lt = random_range(0, 1) == 0;
        
        let inner_abs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            inner_abs,
            Expr::Term(Term::new(-c, 0))
        ])));
        
        let rhs = Expr::Term(Term::new(d, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        let sol = if is_lt {
            SolutionSet::Finite(roots[0], roots[1])
        } else {
            SolutionSet::External(roots[0], roots[1])
        };
        
        return Problem {
            problem_type: ProblemType::AbsoluteValueInequality,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b:0, c:0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Abs Ineq Nested. r={},{}", r1, r2),
        };
    }
}

fn generate_absolute_inequality_quadratic(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-6, 6);
        let r2 = random_range(-6, 6);
        if r1 == r2 { continue; }
        
        let b = -(r1 + r2);
        let c_minus_d = r1 * r2;
        
        let min_2d = (b * b) / 4 - c_minus_d;
        let min_d = (min_2d / 2) + 2;
        
        let d_start = if min_d < 1 { 1 } else { min_d };
        let d = random_range(d_start, d_start + 5);
        
        let c = d + c_minus_d;
        let is_lt = random_range(0, 1) == 0;
        
        let poly = Expr::Sum(vec![
            Expr::Term(Term::new(1, 2)),
            Expr::Term(Term::new(b, 1)),
            Expr::Term(Term::new(c, 0)),
        ]);
        
        let lhs = Expr::Abs(Box::new(poly));
        let rhs = Expr::Term(Term::new(d, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let rel = if is_lt { Relation::Lt } else { Relation::Gt };
        let sol = if is_lt {
            SolutionSet::Finite(roots[0], roots[1])
        } else {
            SolutionSet::External(roots[0], roots[1])
        };

        return Problem {
            problem_type: ProblemType::AbsoluteValueInequality,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b:0, c:0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: rel,
            solution_set: Some(sol),
            explicit_solution: None,
            debug_info: format!("Abs Ineq Quad. r={},{}", r1, r2),
        };
    }
}

fn generate_rational(difficulty: Difficulty) -> Problem {
    
    
    let template = match difficulty {
        Difficulty::Easy => if random_range(0, 2) == 0 { 0 } else { 4 },
        _ => random_range(0, 5),
    };

    match template {
        4 => generate_rational_ratio(difficulty),
        3 => generate_rational_common_denom(difficulty),
        2 => generate_rational_linear_num(difficulty),
        _ => generate_rational_standard(difficulty, template == 1)
    }
}

fn generate_rational_ratio(difficulty: Difficulty) -> Problem {
    
    let r_val = match difficulty {
         Difficulty::Easy => random_range(-10, 10) as f64,
         _ => {
             let d = random_range(1, 6);
             let n = random_range(-10, 10);
             n as f64 / d as f64
         }
    };
    
    
    let c = random_range(1, 5);
    let d = random_range(-10, 10);
    if (c as f64 * r_val + d as f64).abs() < 1e-9 {
         return generate_rational_ratio(difficulty);
    }
    
    let a = random_range(1, 5);
    let b = random_range(-10, 10);
    if (a as f64 * r_val + b as f64).abs() < 1e-9 {
    }
    

    
    
    let e = random_range(-5, 5);
    let f = loop { let v = random_range(1, 6); if v != 0 { break v; } };
    
    let c = random_range(1, 4);
    let d = random_range(-5, 5);
     if (c as f64 * r_val + d as f64).abs() < 1e-9 {
         return generate_rational_ratio(difficulty);
    }
    
    
    for _ in 0..10 {
         let a_try = random_range(-5, 5);
         let b_sol = (e as f64 * (c as f64 * r_val + d as f64) / f as f64) - a_try as f64 * r_val;
         if (b_sol - b_sol.round()).abs() < 1e-9 {
             let b_int = b_sol.round() as i32;
             
             let num_poly = Polynomial::from_terms(&[Term::new(a_try, 1), Term::new(b_int, 0)]);
             let den_poly = Polynomial::from_terms(&[Term::new(c, 1), Term::new(d, 0)]);
             let lhs = Expr::Fraction {
                 num: Box::new(crate::expr::terms_to_expr(num_poly.to_terms())),
                 den: Box::new(crate::expr::terms_to_expr(den_poly.to_terms()))
             };
             
             let rhs = if f == 1 {
                 Expr::Term(Term::new(e, 0))
             } else {
                 Expr::Fraction {
                     num: Box::new(Expr::Term(Term::new(e, 0))),
                     den: Box::new(Expr::Term(Term::new(f, 0)))
                 }
             };
             
             return Problem {
                 problem_type: ProblemType::Rational,
                 difficulty,
                 a: 0, b: 0, c: 0,
                 roots: [r_val, 0.0],
                 root_count: 1,
                 lhs_expr: Some(lhs),
                 rhs_expr: Some(rhs),
                 relation: Relation::Eq, solution_set: None, explicit_solution: None,
                 debug_info: format!("Ratio Gen. r={}", r_val),
             };
         }
    }
    generate_rational_common_denom(difficulty)
}


fn generate_rational_standard(difficulty: Difficulty, split: bool) -> Problem {
    
    loop {
         let (r1, r2) = match difficulty {
             Difficulty::Easy => (random_range(-5, 5) as f64, random_range(-5, 5) as f64),
             _ => {
                 let d = random_range(1, 3);
                 (random_range(-5, 5) as f64 / d as f64, random_range(-5, 5) as f64 / d as f64)
             }
         };
         
         let p = random_range(-6, 6);
         let q = loop { let v = random_range(-6, 6); if v != p { break v; } };
         
         if (r1 - p as f64).abs() < 1e-9 || (r1 - q as f64).abs() < 1e-9 ||
            (r2 - p as f64).abs() < 1e-9 || (r2 - q as f64).abs() < 1e-9 {
                continue;
            }
            
         let k = random_range(1, 3);
         
         
         
         
         
         
         let sum_roots = r1 + r2;
         let prod_roots = r1 * r2;
         
         let s_req = k as f64 * (p as f64 + q as f64 - sum_roots);
         let p_req = k as f64 * (prod_roots - p as f64 * q as f64);
         
         
         let det = p as f64 - q as f64;
         let a_val = (p as f64 * s_req - p_req) / det;
         let b_val = (p_req - q as f64 * s_req) / det;
         
         if (a_val - a_val.round()).abs() < 1e-9 && (b_val - b_val.round()).abs() < 1e-9 {
             let a = a_val.round() as i32;
             let b = b_val.round() as i32;
             if a == 0 || b == 0 { continue; }
             
             let term1 = Expr::Fraction {
                 num: Box::new(Expr::Term(Term::new(a, 0))),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-p, 0))]))
             };
             let term2 = Expr::Fraction {
                 num: Box::new(Expr::Term(Term::new(b, 0))),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-q, 0))]))
             };
             
             let (lhs, rhs) = if split {
                 (
                     term1,
                     Expr::Sum(vec![
                         Expr::Term(Term::new(k, 0)),
                         Expr::MonomialMul{ coeff: -1, exp:0, inner: Box::new(term2) }
                     ])
                 )
             } else {
                 (
                     Expr::Sum(vec![term1, term2]),
                     Expr::Term(Term::new(k, 0))
                 )
             };
             
              return Problem {
                 problem_type: ProblemType::Rational,
                 difficulty,
                 a: 0, b: 0, c: 0,
                 roots: [r1, r2],
                 root_count: 2,
                 lhs_expr: Some(lhs),
                 rhs_expr: Some(rhs),
                 relation: Relation::Eq, solution_set: None, explicit_solution: None,
                 debug_info: format!("Std Rational. r={:.2},{:.2}", r1, r2),
             };
         }
    }
}

fn generate_rational_linear_num(difficulty: Difficulty) -> Problem {
    
    
    loop {
         let (r1, r2) = match difficulty {
             Difficulty::Easy => (random_range(-5, 5) as f64, random_range(-5, 5) as f64),
             _ => {
                 let d = random_range(1, 3);
                 (random_range(-5, 5) as f64 / d as f64, random_range(-5, 5) as f64 / d as f64)
             }
         };
         let p = random_range(-5, 5);
         let q = loop { let v = random_range(-5, 5); if v != p { break v; } };
         
         let k = random_range(1, 3);
         let a = loop { let v = random_range(1, 4); if v != k { break v; } };
         
         
         
         
         let lead = (a - k) as f64;
         let rhs_x = -lead * (r1 + r2) + (a as f64 * q as f64) - (k as f64 * (p as f64 + q as f64));
         let rhs_c = lead * (r1 * r2) + (k as f64 * p as f64 * q as f64);
         
         let det = p as f64 - q as f64;
         let b_val = (p as f64 * rhs_x + rhs_c) / det;
         let c_val_alt = b_val - rhs_x;
         
         if (b_val - b_val.round()).abs() < 1e-9 && (c_val_alt - c_val_alt.round()).abs() < 1e-9 {
              let b = b_val.round() as i32;
              let c = c_val_alt.round() as i32;
              if c == 0 { continue; }
              
              let term1 = Expr::Fraction {
                 num: Box::new(Expr::Sum(vec![Expr::Term(Term::new(a, 1)), Expr::Term(Term::new(b, 0))])),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-p, 0))]))
              };
              let term2 = Expr::Fraction {
                 num: Box::new(Expr::Term(Term::new(c, 0))),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-q, 0))]))
              };
              
              let lhs = term1;
              let rhs = Expr::Sum(vec![
                  Expr::Term(Term::new(k, 0)),
                  term2
              ]);
              
              return Problem {
                 problem_type: ProblemType::Rational,
                 difficulty,
                 a: 0, b: 0, c: 0,
                 roots: [r1, r2],
                 root_count: 2,
                 lhs_expr: Some(lhs),
                 rhs_expr: Some(rhs),
                 relation: Relation::Eq, solution_set: None, explicit_solution: None,
                 debug_info: format!("Linear Num Gen. r={:.2},{:.2}", r1, r2),
             };
         }
    }
}

fn generate_rational_common_denom(difficulty: Difficulty) -> Problem {
    
    
    loop {
         let (r1, r2) = match difficulty {
             Difficulty::Easy => (random_range(-5, 5) as f64, random_range(-5, 5) as f64),
             _ => {
                 let d = random_range(1, 3);
                 (random_range(-5, 5) as f64 / d as f64, random_range(-5, 5) as f64 / d as f64)
             }
         };
         
         
         let p = random_range(-5, 5);
         let q = loop { let v = random_range(-5, 5); if v != p { break v; } };
         
         let _k = 1;
         
         let a = random_range(-5, 5);
         let b = random_range(-5, 5);
         if a == 0 || b == 0 { continue; }
         
         let lhs_x = a + b;
         let lhs_c = -(a*q + b*p);
         
         
         let q_x = -1.0 * (r1 + r2);
         let q_constant = r1 * r2;
         
         let rhs_quad_coeff = 1;
         let rhs_linear_coeff = q_x + lhs_x as f64;
         let rhs_const_coeff = q_constant + lhs_c as f64;
         
         if (rhs_linear_coeff - rhs_linear_coeff.round()).abs() < 1e-9 &&
            (rhs_const_coeff - rhs_const_coeff.round()).abs() < 1e-9 {
            
             let c = rhs_quad_coeff;
             let d = rhs_linear_coeff.round() as i32;
             let e = rhs_const_coeff.round() as i32;
             
             let term1 = Expr::Fraction {
                 num: Box::new(Expr::Term(Term::new(a, 0))),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-p, 0))]))
             };
             let term2 = Expr::Fraction {
                 num: Box::new(Expr::Term(Term::new(b, 0))),
                 den: Box::new(Expr::Sum(vec![Expr::Term(Term::new(1, 1)), Expr::Term(Term::new(-q, 0))]))
             };
             
             let lhs = Expr::Sum(vec![term1, term2]);
             
             let rhs_num = Polynomial::from_terms(&[
                 Term::new(c, 2), Term::new(d, 1), Term::new(e, 0)
             ]);
             let den_poly = Polynomial::from_terms(&[
                 Term::new(1, 2), Term::new(-(p+q), 1), Term::new(p*q, 0)
             ]);
             
             let rhs = Expr::Fraction {
                 num: Box::new(crate::expr::terms_to_expr(rhs_num.to_terms())),
                 den: Box::new(crate::expr::terms_to_expr(den_poly.to_terms()))
             };
             
             return Problem {
                 problem_type: ProblemType::Rational,
                 difficulty,
                 a: 0, b: 0, c: 0,
                 roots: [r1, r2],
                 root_count: 2,
                 lhs_expr: Some(lhs),
                 rhs_expr: Some(rhs),
                 relation: Relation::Eq, solution_set: None, explicit_solution: None,
                 debug_info: format!("Common Denom Gen. r={:.2},{:.2}", r1, r2),
             };
         }
    }
}

fn generate_irrational(difficulty: Difficulty) -> Problem {
    
    let template = match difficulty {
        Difficulty::Easy => if random_range(0, 2) == 0 { 0 } else { 1 },
        Difficulty::Medium => random_range(2, 4),
        Difficulty::Hard => random_range(4, 9),
    };

    match template {
        8 => generate_irrational_nested_radical(difficulty),
        7 => generate_irrational_radical_difference(difficulty),
        6 => generate_irrational_triple(difficulty),
        5 => generate_irrational_advanced_isolation(difficulty),
        4 => generate_irrational_double(difficulty),
        3 => generate_irrational_two_radicals(difficulty),
        2 => generate_irrational_linear_rhs(difficulty),
        1 => generate_irrational_displaced(difficulty),
        _ => generate_irrational_simple(difficulty),
    }
}

fn generate_irrational_simple(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-10, 10);
        let c = random_range(1, 10);
        let val_sq = c * c;
        
        let a = loop { let v = random_range(1, 6); if v != 0 { break v; } };
        let b = val_sq - a * x;
        
        if b.abs() > 50 { continue; }
        
        let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Term(Term::new(c, 0));
        
        return Problem {
            problem_type: ProblemType::Irrational,
            difficulty,
            a: 0, b: 0, c: 0,
            roots: [x as f64, 0.0],
            root_count: 1,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Irr Simple. x={}", x),
        };
    }
}

fn generate_irrational_displaced(difficulty: Difficulty) -> Problem {
    loop {
        let p = generate_irrational_simple(difficulty);
        let k = 
        if let Some(Expr::Term(t)) = p.rhs_expr {
             t.coeff
        } else { continue };
        
        let c = random_range(-10, 10);
        let d = k + c;
        
        let lhs = Expr::Sum(vec![
            p.lhs_expr.unwrap(),
            Expr::Term(Term::new(c, 0))
        ]);
        let rhs = Expr::Term(Term::new(d, 0));
        
        return Problem {
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            ..p
        };
    }
}

fn generate_irrational_linear_rhs(difficulty: Difficulty) -> Problem {
     
     loop {
         let x = random_range(-10, 10);
         let c = random_range(1, 4);
         let d = random_range(-10, 10);
         
         let rhs_val = c * x + d;
         if rhs_val < 0 { continue; }
         
         let val_sq = rhs_val * rhs_val;
         
         let a = loop { let v = random_range(1, 6); if v != 0 { break v; } };
         let b = val_sq - a * x;
         
         if b.abs() > 100 { continue; }
         
         let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(a, 1)),
             Expr::Term(Term::new(b, 0))
         ])));
         let rhs = Expr::Sum(vec![
             Expr::Term(Term::new(c, 1)),
             Expr::Term(Term::new(d, 0))
         ]);
         
         return Problem {
             problem_type: ProblemType::Irrational,
             difficulty,
             a: 0, b:0, c:0,
             roots: [x as f64, 0.0],
             root_count: 1,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Irr Linear RHS. x={}", x),
         };
     }
}

fn generate_irrational_two_radicals(difficulty: Difficulty) -> Problem {
    
    loop {
        let x = random_range(-10, 10);
        let val = random_range(0, 50);
        
        let a = random_range(1, 5);
        let c = loop { let v = random_range(1, 5); if v != a { break v; } };
        
        let b = val - a * x;
        let d = val - c * x;
        
        let lhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(a, 1)),
             Expr::Term(Term::new(b, 0))
         ])));
         let rhs = Expr::Sqrt(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(c, 1)),
             Expr::Term(Term::new(d, 0))
         ])));
         
         return Problem {
             problem_type: ProblemType::Irrational,
             difficulty,
             roots: [x as f64, 0.0],
             root_count: 1,
             a: 0, b: 0, c: 0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Two Radicals. x={}", x),
         };
    }
}

fn generate_irrational_double(difficulty: Difficulty) -> Problem {
    
    loop {
        let x = random_range(-10, 10);
        let v1 = random_range(1, 8);
        let v2 = random_range(1, 8);
        let e = v1 + v2;
        
        let sq1 = v1 * v1;
        let sq2 = v2 * v2;
        
        let a = loop { let v = random_range(1, 5); if v != 0 { break v; } };
        let b = sq1 - a * x;
        
        let c = loop { let v = random_range(1, 5); if v != 0 { break v; } };
        let d = sq2 - c * x;
        
        let lhs = Expr::Sum(vec![
             Expr::Sqrt(Box::new(Expr::Sum(vec![
                 Expr::Term(Term::new(a, 1)),
                 Expr::Term(Term::new(b, 0))
             ]))),
             Expr::Sqrt(Box::new(Expr::Sum(vec![
                 Expr::Term(Term::new(c, 1)),
                 Expr::Term(Term::new(d, 0))
             ])))
         ]);
        let rhs = Expr::Term(Term::new(e, 0));
        
        return Problem {
             problem_type: ProblemType::Irrational,
             difficulty,
             roots: [x as f64, 0.0],
             root_count: 1,
             a: 0, b: 0, c: 0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Double Radical. x={}, v1={}, v2={}", x, v1, v2),
         };
    }
}

fn generate_absolute(difficulty: Difficulty) -> Problem {
    
    let template = match difficulty {
        Difficulty::Easy => 0,
        Difficulty::Medium => random_range(0, 3),
        Difficulty::Hard => random_range(1, 7),
    };

    match template {
        6 => generate_absolute_double_nested(difficulty),
        5 => generate_absolute_quadratic_rhs(difficulty),
        4 => generate_absolute_quadratic(difficulty),
        3 => generate_absolute_nested(difficulty),
        2 => generate_absolute_two_abs(difficulty),
        1 => generate_absolute_linear_rhs(difficulty),
        _ => generate_absolute_simple(difficulty),
    }
}

fn generate_absolute_simple(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-10, 10);
        let r2 = random_range(-10, 10);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 4);
        
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let c = (a * diff) / 2;
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Term(Term::new(c, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());

        return Problem {
             problem_type: ProblemType::AbsoluteValue,
             difficulty,
             roots,
             root_count: 2,
             a: 0, b: 0, c: 0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Abs Simple. r={},{}. A={}", r1, r2, a),
        }
    }
}

fn generate_absolute_linear_rhs(difficulty: Difficulty) -> Problem {
     
     loop {
         let r1 = random_range(-8, 8);
         let r2 = random_range(-8, 8);
         if r1 == r2 { continue; }
         
         
         let a = random_range(1, 5);
         let c = random_range(1, 5);
         if a == c { continue; }
         
         
         
         let two_d = a * (r1 - r2) - c * (r1 + r2);
         let two_b = -a * (r1 + r2) + c * (r1 - r2);
         
         if two_d % 2 != 0 || two_b % 2 != 0 { continue; }
         
         let d = two_d / 2;
         let b = two_b / 2;
         
         if c * r1 + d < 0 || c * r2 + d < 0 { continue; }
         
         let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(a, 1)),
             Expr::Term(Term::new(b, 0))
         ])));
         let rhs = Expr::Sum(vec![
             Expr::Term(Term::new(c, 1)),
             Expr::Term(Term::new(d, 0))
         ]);
         
         let mut roots = [r1 as f64, r2 as f64];
         roots.sort_by(|a, b| a.partial_cmp(b).unwrap());

         return Problem {
             problem_type: ProblemType::AbsoluteValue,
             difficulty,
             roots,
             root_count: 2,
             a: 0, b:0, c:0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Abs Linear RHS. r={},{}. A={}, C={}", r1, r2, a, c),
         };
     }
}

fn generate_absolute_two_abs(difficulty: Difficulty) -> Problem {
    
      loop {
         let r1 = random_range(-8, 8); 
         let r2 = random_range(-8, 8);
         if r1 == r2 { continue; }
         
         let a = random_range(1, 5);
         let c = loop { let v = random_range(1, 5); if v != a { break v; } };
         
         let two_d = a * (r1 - r2) - c * (r1 + r2);
         let two_b = -a * (r1 + r2) + c * (r1 - r2);
         
         if two_d % 2 != 0 || two_b % 2 != 0 { continue; }
         
         let d = two_d / 2;
         let b = two_b / 2;
         
         let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(a, 1)),
             Expr::Term(Term::new(b, 0))
         ])));
         let rhs = Expr::Abs(Box::new(Expr::Sum(vec![
             Expr::Term(Term::new(c, 1)),
             Expr::Term(Term::new(d, 0))
         ])));
         
         let mut roots = [r1 as f64, r2 as f64];
         roots.sort_by(|a, b| a.partial_cmp(b).unwrap());

         return Problem {
             problem_type: ProblemType::AbsoluteValue,
             difficulty,
             roots,
             root_count: 2,
             a: 0, b:0, c:0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Two Abs. r={},{}.", r1, r2),
         };
     }
}

fn generate_absolute_nested(difficulty: Difficulty) -> Problem {
    
    
    loop {
        let r1 = random_range(-8, 8);
        let r2 = random_range(-8, 8);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 4);
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let k = (a * diff) / 2;
        
        let min_d = (k / 2) + 1;
        let d = random_range(min_d, min_d + 5);
        let c = k - d;
        
        if c == 0 { continue; }
        
        let inner_abs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            inner_abs,
            Expr::Term(Term::new(-c, 0))
        ])));
         
        let rhs = Expr::Term(Term::new(d, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
         return Problem {
             problem_type: ProblemType::AbsoluteValue,
             difficulty,
             roots,
             root_count: 2,
             a: 0, b:0, c:0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Nested Abs. r={},{}. K={}", r1, r2, k),
         };
    }
}

fn generate_absolute_quadratic(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-6, 6);
        let r2 = random_range(-6, 6);
        if r1 == r2 { continue; }
        
        
        let b = -(r1 + r2);
        let c_minus_d = r1 * r2;
        
        
        
        let min_2d = (b * b) / 4 - c_minus_d;
        let min_d = (min_2d / 2) + 2; 
        
        let d_start = if min_d < 1 { 1 } else { min_d };
        let d = random_range(d_start, d_start + 5);
        
        let c = d + c_minus_d;
        
        let poly = Expr::Sum(vec![
             Expr::Term(Term::new(1, 2)),
             Expr::Term(Term::new(b, 1)),
             Expr::Term(Term::new(c, 0)),
        ]);
        
        let lhs = Expr::Abs(Box::new(poly));
        let rhs = Expr::Term(Term::new(d, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());

         return Problem {
             problem_type: ProblemType::AbsoluteValue,
             difficulty,
             roots,
             root_count: 2,
             a: 0, b:0, c:0,
             lhs_expr: Some(lhs),
             rhs_expr: Some(rhs),
             relation: Relation::Eq, solution_set: None, explicit_solution: None,
             debug_info: format!("Abs Quad. r={},{}. D={}", r1, r2, d),
         };
    }
}

fn generate_irrational_advanced_isolation(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-8, 8);
        let v = random_range(2, 7);
        let sq = v * v;
        
        let a = random_range(1, 4);
        let b = sq - a * x;
        
        let c = random_range(1, 3);
        let d = random_range(-8, 8);
        let k = v - (c * x + d);
        
        if b.abs() > 60 || k.abs() > 15 { continue; }
        if c * x + d < 0 { continue; }
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a, 1)),
                Expr::Term(Term::new(b, 0))
            ]))),
            Expr::Term(Term::new(c, 1)),
            Expr::Term(Term::new(d, 0))
        ]);
        let rhs = Expr::Term(Term::new(v, 0));
        
        return Problem {
            problem_type: ProblemType::Irrational,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Irr Adv Isolation. x={}", x),
        };
    }
}

fn generate_irrational_triple(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-6, 6);
        let v1 = random_range(1, 5);
        let v2 = random_range(1, 5);
        let v3 = random_range(1, 5);
        let e = v1 + v2 + v3;
        
        let sq1 = v1 * v1;
        let sq2 = v2 * v2;
        let sq3 = v3 * v3;
        
        let a1 = random_range(1, 4);
        let b1 = sq1 - a1 * x;
        
        let a2 = random_range(1, 4);
        let b2 = sq2 - a2 * x;
        
        let a3 = random_range(1, 4);
        let b3 = sq3 - a3 * x;
        
        if b1.abs() > 40 || b2.abs() > 40 || b3.abs() > 40 { continue; }
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a1, 1)),
                Expr::Term(Term::new(b1, 0))
            ]))),
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a2, 1)),
                Expr::Term(Term::new(b2, 0))
            ]))),
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a3, 1)),
                Expr::Term(Term::new(b3, 0))
            ])))
        ]);
        let rhs = Expr::Term(Term::new(e, 0));
        
        return Problem {
            problem_type: ProblemType::Irrational,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Triple Radical. x={}", x),
        };
    }
}

fn generate_absolute_quadratic_rhs(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-6, 6);
        let r2 = random_range(-6, 6);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 3);
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let k = (a * diff) / 2;
        
        let c = 1;
        let d = random_range(-3, 3);
        let e = k - c * r1 * r1 - d * r1;
        let e2 = k - c * r2 * r2 - d * r2;
        
        if e != e2 { continue; }
        if c * r1 * r1 + d * r1 + e < 0 || c * r2 * r2 + d * r2 + e < 0 { continue; }
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        let rhs = Expr::Sum(vec![
            Expr::Term(Term::new(c, 2)),
            Expr::Term(Term::new(d, 1)),
            Expr::Term(Term::new(e, 0))
        ]);
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        return Problem {
            problem_type: ProblemType::AbsoluteValue,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Abs Quad RHS. r={},{}", r1, r2),
        };
    }
}

fn generate_absolute_double_nested(difficulty: Difficulty) -> Problem {
    loop {
        let r1 = random_range(-5, 5);
        let r2 = random_range(-5, 5);
        if r1 == r2 { continue; }
        
        let a = random_range(1, 3);
        let sum = r1 + r2;
        let diff = (r1 - r2).abs();
        
        if (a * sum) % 2 != 0 || (a * diff) % 2 != 0 { continue; }
        
        let b = -(a * sum) / 2;
        let k1 = (a * diff) / 2;
        
        let c1 = random_range(1, 4);
        if c1 == 0 { continue; }
        let min_d1 = (k1 / 2).max(1);
        let d1 = random_range(min_d1, min_d1 + 3);
        let k2 = k1 - d1;
        if k2 == 0 { continue; }
        
        let c2 = random_range(1, 4);
        if c2 == 0 { continue; }
        let min_d2 = (k2 / 2).max(1);
        let d2 = random_range(min_d2, min_d2 + 3);
        
        let inner_abs = Expr::Abs(Box::new(Expr::Sum(vec![
            Expr::Term(Term::new(a, 1)),
            Expr::Term(Term::new(b, 0))
        ])));
        
        let middle_abs = Expr::Abs(Box::new(Expr::Sum(vec![
            inner_abs,
            Expr::Term(Term::new(-k2, 0))
        ])));
        
        let lhs = Expr::Abs(Box::new(Expr::Sum(vec![
            middle_abs,
            Expr::Term(Term::new(-c2, 0))
        ])));
        
        let rhs = Expr::Term(Term::new(d2, 0));
        
        let mut roots = [r1 as f64, r2 as f64];
        roots.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        return Problem {
            problem_type: ProblemType::AbsoluteValue,
            difficulty,
            roots,
            root_count: 2,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Double Nested Abs. r={},{}", r1, r2),
        };
    }
}

fn generate_irrational_radical_difference(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-8, 8);
        let v1 = random_range(3, 9);
        let v2 = random_range(2, 6);
        
        if v1 <= v2 { continue; }
        let e = v1 - v2;
        
        let sq1 = v1 * v1;
        let sq2 = v2 * v2;
        
        let a1 = random_range(1, 4);
        let b1 = sq1 - a1 * x;
        
        let a2 = random_range(1, 4);
        let b2 = sq2 - a2 * x;
        
        if b1.abs() > 50 || b2.abs() > 50 { continue; }
        if b1 < 0 || b2 < 0 { continue; }
        
        let lhs = Expr::Sum(vec![
            Expr::Sqrt(Box::new(Expr::Sum(vec![
                Expr::Term(Term::new(a1, 1)),
                Expr::Term(Term::new(b1, 0))
            ]))),
            Expr::MonomialMul {
                coeff: -1,
                exp: 0,
                inner: Box::new(Expr::Sqrt(Box::new(Expr::Sum(vec![
                    Expr::Term(Term::new(a2, 1)),
                    Expr::Term(Term::new(b2, 0))
                ]))))
            }
        ]);
        let rhs = Expr::Term(Term::new(e, 0));
        
        return Problem {
            problem_type: ProblemType::Irrational,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Radical Difference. x={}", x),
        };
    }
}

fn generate_irrational_nested_radical(difficulty: Difficulty) -> Problem {
    loop {
        let x = random_range(-6, 6);
        let inner_val = random_range(1, 8);
        let outer_val = random_range(2, 6);
        
        let inner_sq = inner_val * inner_val;
        let outer_sq = outer_val * outer_val;
        
        let a_inner = random_range(1, 3);
        let b_inner = inner_sq - a_inner * x;
        
        if b_inner < 0 || b_inner.abs() > 40 { continue; }
        
        let radicand_value_at_x = a_inner * x + b_inner;
        if radicand_value_at_x < 0 { continue; }
        
        let expected_sqrt = inner_val;
        
        let a_outer = random_range(1, 3);
        let b_outer = outer_sq - a_outer * expected_sqrt;
        
        if b_outer < 0 || b_outer.abs() > 30 { continue; }
        
        let inner_radical = Expr::Sum(vec![
            Expr::Term(Term::new(a_inner, 1)),
            Expr::Term(Term::new(b_inner, 0))
        ]);
        
        let nested_content = Expr::Sum(vec![
            Expr::MonomialMul {
                coeff: a_outer,
                exp: 0,
                inner: Box::new(Expr::Sqrt(Box::new(inner_radical)))
            },
            Expr::Term(Term::new(b_outer, 0))
        ]);
        
        let lhs = Expr::Sqrt(Box::new(nested_content));
        let rhs = Expr::Term(Term::new(outer_val, 0));
        
        return Problem {
            problem_type: ProblemType::Irrational,
            difficulty,
            roots: [x as f64, 0.0],
            root_count: 1,
            a: 0, b: 0, c: 0,
            lhs_expr: Some(lhs),
            rhs_expr: Some(rhs),
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: format!("Nested Radical. x={}", x),
        };
    }
}

pub(crate) fn random_range(min: i32, max: i32) -> i32 {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    rng.gen_range(min..=max)
}

fn generate_linear(difficulty: Difficulty) -> Problem {
    let use_integer = match difficulty {
        Difficulty::Easy => true,
        Difficulty::Medium => random_range(0, 3) == 0,
        Difficulty::Hard => random_range(0, 5) == 0,
    };

    let (m, q, root_val) = if use_integer {
         let (min, max) = match difficulty {
            Difficulty::Easy => (-10, 10),
            Difficulty::Medium => (-20, 20),
            Difficulty::Hard => (-50, 50),
        };
        
        let root = random_range(min, max);
        let m = loop {
            let val = random_range(min, max);
            if val != 0 { break val; }
        };
        let q = -m * root;
        (m, q, root as f64)
    } else {
        let (n_range, d_range, k_range) = match difficulty {
            Difficulty::Easy => (10, 1, 1),
            Difficulty::Medium => (20, 10, 3),
            Difficulty::Hard => (50, 20, 5),
        };
        
        let n = random_range(-n_range, n_range);
        let d = loop {
            let val = random_range(2, d_range);
             break val;
        };
        
        let k = if k_range > 1 {
             loop {
                 let val = random_range(-k_range, k_range);
                 if val != 0 { break val; }
             }
        } else { 1 };
        
        let m = d * k;
        let q_val = -n * k;
        
        (m, q_val, n as f64 / d as f64)
    };
    
    let target_poly = Polynomial::from_terms(&[
        Term::new(m, 1),
        Term::new(q, 0),
    ]);

    let obfuscated = obfuscate(&target_poly, &difficulty);
    
    Problem {
        problem_type: ProblemType::Linear,
        difficulty,
        a: m,
        b: q,
        c: 0,
        roots: [root_val, 0.0],
        root_count: 1,
        lhs_expr: Some(obfuscated.lhs),
        rhs_expr: Some(obfuscated.rhs),
        relation: Relation::Eq, solution_set: None, explicit_solution: None,
        debug_info: format!("Linear Gen. m={}, q={}, root={:.2}", m, q, root_val),
    }
}

fn generate_quadratic(difficulty: Difficulty) -> Problem {
    match difficulty {
        Difficulty::Easy => {
            let r1 = random_range(-10, 10);
            let r2 = random_range(-10, 10);
            let a = 1;
            let b = -a * (r1 + r2);
            let c = a * r1 * r2;
            
            let target_poly = Polynomial::from_terms(&[
                Term::new(a, 2),
                Term::new(b, 1),
                Term::new(c, 0),
            ]);
            let obfuscated = obfuscate(&target_poly, &difficulty);

            Problem {
                problem_type: ProblemType::Quadratic,
                difficulty,
                a, b, c,
                roots: [r1 as f64, r2 as f64],
                root_count: 2,
                lhs_expr: Some(obfuscated.lhs),
                rhs_expr: Some(obfuscated.rhs),
                relation: Relation::Eq, solution_set: None, explicit_solution: None,
                debug_info: format!("Quad Easy. r1={}, r2={}", r1, r2),
            }
        }
        Difficulty::Medium => {
            let d = random_range(1, 4);
            let e = random_range(1, 4);
            let n = random_range(-10, 10);
            let m = random_range(-10, 10);
            
            let a = d * e;
            let b = -(d * m + e * n);
            let c = n * m;

            let target_poly = Polynomial::from_terms(&[
                Term::new(a, 2),
                Term::new(b, 1),
                Term::new(c, 0),
            ]);
            let obfuscated = obfuscate(&target_poly, &difficulty);
            
            Problem {
                problem_type: ProblemType::Quadratic,
                difficulty,
                a, b, c,
                roots: [n as f64 / d as f64, m as f64 / e as f64],
                root_count: 2,
                lhs_expr: Some(obfuscated.lhs),
                rhs_expr: Some(obfuscated.rhs),
                relation: Relation::Eq, solution_set: None, explicit_solution: None,
                debug_info: format!("Quad Medium. Roots: {}/{}, {}/{}", n, d, m, e),
            }
        }
        Difficulty::Hard => {
            if random_range(0, 1) == 0 {
                let p = random_range(-6, 6);
                let q = loop {
                   let val = random_range(2, 20);
                   let sqrt = (val as f64).sqrt();
                   if (sqrt - sqrt.round()).abs() > 1e-9 { break val; }
                };
                
                let a = 1;
                let b = -2 * p;
                let c = p * p - q;
                
                let target_poly = Polynomial::from_terms(&[
                    Term::new(a, 2),
                    Term::new(b, 1),
                    Term::new(c, 0),
                ]);
                let obfuscated = obfuscate(&target_poly, &difficulty);
                
                let sqrt_q = (q as f64).sqrt();
                
                 Problem {
                    problem_type: ProblemType::Quadratic,
                    difficulty,
                    a, b, c,
                    roots: [p as f64 - sqrt_q, p as f64 + sqrt_q],
                    root_count: 2,
                    lhs_expr: Some(obfuscated.lhs),
                    rhs_expr: Some(obfuscated.rhs),
                    relation: Relation::Eq, solution_set: None, explicit_solution: Some(format!("x = {} \\pm \\sqrt{{{}}}", p, q)),
                    debug_info: format!("Quad Hard Surd. p={}, q={}", p, q),
                }
            } else {
                 let d = random_range(2, 6);
                 let e = random_range(2, 6);
                 let n = random_range(-15, 15);
                 let m = random_range(-15, 15);
                 
                 let a = d * e;
                 let b = -(d * m + e * n);
                 let c = n * m;
                 
                  let target_poly = Polynomial::from_terms(&[
                    Term::new(a, 2),
                    Term::new(b, 1),
                    Term::new(c, 0),
                ]);
                let obfuscated = obfuscate(&target_poly, &difficulty);

                 Problem {
                    problem_type: ProblemType::Quadratic,
                    difficulty,
                    a, b, c,
                    roots: [n as f64 / d as f64, m as f64 / e as f64],
                    root_count: 2,
                    lhs_expr: Some(obfuscated.lhs),
                    rhs_expr: Some(obfuscated.rhs),
                    relation: Relation::Eq, solution_set: None, explicit_solution: None,
                    debug_info: format!("Quad Hard Rational. Roots: {}/{}, {}/{}", n, d, m, e),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quadratic_formatting() {
        let p = Problem {
            problem_type: ProblemType::Quadratic,
            difficulty: Difficulty::Easy,
            a: 1,
            b: -5,
            c: 6,
            roots: [2.0, 3.0],
            root_count: 2,
            lhs_expr: None,
            rhs_expr: None,
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: String::new(),
        };
        assert_eq!(p.to_latex(), "x^2 - 5x + 6 = 0");
    }

    #[test]
    fn test_quadratic_no_middle_term() {
        let p = Problem {
            problem_type: ProblemType::Quadratic,
            difficulty: Difficulty::Easy,
            a: 1,
            b: 0,
            c: -4,
            roots: [-2.0, 2.0],
            root_count: 2,
            lhs_expr: None,
            rhs_expr: None,
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: String::new(),
        };
        assert_eq!(p.to_latex(), "x^2 - 4 = 0");
    }

    #[test]
    fn test_quadratic_negative_leading() {
        let p = Problem {
            problem_type: ProblemType::Quadratic,
            difficulty: Difficulty::Hard,
            a: -1,
            b: 1,
            c: 2,
            roots: [-1.0, 2.0],
            root_count: 2,
            lhs_expr: None,
            rhs_expr: None,
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: String::new(),
        };
        assert_eq!(p.to_latex(), "-x^2 + x + 2 = 0");
    }

    #[test]
    fn test_linear_formatting() {
        let p = Problem {
            problem_type: ProblemType::Linear,
            difficulty: Difficulty::Easy,
            a: 2,
            b: -6,
            c: 0,
            roots: [3.0, 0.0],
            root_count: 1,
            lhs_expr: None,
            rhs_expr: None,
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: String::new(),
        };
        assert_eq!(p.to_latex(), "2x - 6 = 0");
    }

    #[test]
    fn test_rational_generation() {
        for _ in 0..10 {
            let p = generate_rational(Difficulty::Medium);
            assert_eq!(p.problem_type, ProblemType::Rational);
            assert!(p.lhs_expr.is_some());
            assert!(p.rhs_expr.is_some());
            assert!(p.root_count == 1 || p.root_count == 2);
        }
    }

    #[test]
    fn test_irrational_generation() {
        for _ in 0..10 {
            let p = generate_irrational(Difficulty::Medium);
            assert_eq!(p.problem_type, ProblemType::Irrational);
            assert!(p.lhs_expr.is_some());
            assert!(p.rhs_expr.is_some());
            assert!(p.root_count >= 1);
        }
    }

    #[test]
    fn test_absolute_generation() {
        for _ in 0..10 {
            let p = generate_absolute(Difficulty::Medium);
            assert_eq!(p.problem_type, ProblemType::AbsoluteValue);
            assert!(p.lhs_expr.is_some());
            assert!(p.rhs_expr.is_some());
            assert_eq!(p.root_count, 2);
        }
    }
    #[test]
    fn test_impossible_solution_string() {
        let p = Problem {
            problem_type: ProblemType::Quadratic,
            difficulty: Difficulty::Hard,
            a: 1,
            b: 0,
            c: 1,
            roots: [0.0; 2],
            root_count: 0,
            lhs_expr: None,
            rhs_expr: None,
            relation: Relation::Eq, solution_set: None, explicit_solution: None,
            debug_info: String::new(),
        };
        assert_eq!(p.solution_latex(), "impossible");
    }
}
