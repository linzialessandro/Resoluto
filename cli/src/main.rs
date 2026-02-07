use clap::Parser;
use resoluto_core::{generate_problem, Difficulty, ProblemType};

#[derive(Parser)]
#[command(name = "resoluto")]
#[command(about = "A deterministic mathematical problem generator", long_about = None)]
struct Args {
    #[arg(short = 'n', long, default_value_t = 5)]
    count: usize,

    #[arg(short, long, value_enum, default_value_t = DifficultyArg::Easy)]
    difficulty: DifficultyArg,

    #[arg(short = 't', long, value_enum, default_value_t = ProblemTypeArg::Quadratic)]
    problem_type: ProblemTypeArg,
}

#[derive(clap::ValueEnum, Clone)]
enum DifficultyArg {
    Easy,
    Medium,
    Hard,
}

impl From<DifficultyArg> for Difficulty {
    fn from(d: DifficultyArg) -> Self {
        match d {
            DifficultyArg::Easy => Difficulty::Easy,
            DifficultyArg::Medium => Difficulty::Medium,
            DifficultyArg::Hard => Difficulty::Hard,
        }
    }
}

#[derive(clap::ValueEnum, Clone)]
enum ProblemTypeArg {
    Linear,
    Quadratic,
    Rational,
    Irrational,
    AbsoluteValue,
}

impl From<ProblemTypeArg> for ProblemType {
    fn from(t: ProblemTypeArg) -> Self {
        match t {
            ProblemTypeArg::Linear => ProblemType::Linear,
            ProblemTypeArg::Quadratic => ProblemType::Quadratic,
            ProblemTypeArg::Rational => ProblemType::Rational,
            ProblemTypeArg::Irrational => ProblemType::Irrational,
            ProblemTypeArg::AbsoluteValue => ProblemType::AbsoluteValue,
        }
    }
}

fn main() {
    let args = Args::parse();
    
    let difficulty: Difficulty = args.difficulty.into();
    let problem_type: ProblemType = args.problem_type.into();
    
    let problems: Vec<_> = (0..args.count)
        .map(|_| generate_problem(problem_type, difficulty))
        .collect();
    
    println!("## Exercises\n");
    for (i, problem) in problems.iter().enumerate() {
        println!("{}. ${}$", i + 1, problem.to_latex());
    }
    
    println!("\n## Solutions\n");
    for (i, problem) in problems.iter().enumerate() {
        println!("{}. ${}$", i + 1, problem.solution_latex());
    }
}
