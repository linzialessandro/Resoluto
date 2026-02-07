<div align="center">
  <img src="web/logo.png" width="150" alt="Resoluto Logo" />
  <h1>Resoluto</h1>
  <p><strong>A free, open-source mathematical problem generator for educators</strong></p>
</div>

[![Deploy to GitHub Pages](https://github.com/linzialessandro/Resoluto/actions/workflows/deploy.yml/badge.svg)](https://github.com/linzialessandro/Resoluto/actions/workflows/deploy.yml)

Resoluto is a tool built by a mathematics teacher for fellow educators. It generates exercises by starting with the solution and working backwards, ensuring every problem has clean, integer or rational solutions.

**[Try the Live Demo →](https://linzialessandro.github.io/Resoluto/)**

---

## Features

### Problem Types

| Type | Description | Difficulty Levels |
|------|-------------|-------------------|
| **Linear Equations** | `mx + q = 0` | Easy, Medium, Hard |
| **Quadratic Equations** | `ax² + bx + c = 0` | Easy, Medium, Hard |
| **Rational Equations** | Equations with fractions like `A/(x-p) + B/(x-q) = K` | Easy, Medium, Hard |
| **Irrational Equations** | Equations with square roots like `√(Ax+B) = C` | Easy, Medium, Hard |
| **Absolute Value Equations** | Equations with `|...|` like `|Ax+B| = C` | Easy, Medium, Hard |

### Core Capabilities

- **Deterministic Generation**: Problems are generated backwards from roots, guaranteeing solvable equations
- **Clean Solutions**: Integer or simple rational solutions—no messy decimals
- **LaTeX Output**: Properly formatted mathematical notation for beautiful rendering
- **Multiple Interfaces**: CLI for scripting, Web app for interactive use
- **Difficulty Scaling**: Coefficients and structures adjust based on difficulty level

---

## Architecture

Resoluto is structured as a Rust workspace with three crates:

```
Resoluto/
├── core/               # Pure Rust library with all mathematical logic
│   └── src/
│       ├── lib.rs      # Problem generation algorithms
│       ├── expr.rs     # Expression AST and LaTeX rendering
│       ├── polynomial.rs   # Polynomial arithmetic
│       └── obfuscate.rs    # Equation obfuscation (adds visual complexity)
├── cli/                # Command-line interface
│   └── src/main.rs
├── web/                # WebAssembly frontend (Yew framework)
│   ├── src/main.rs
│   ├── index.html
│   └── styles.css
└── Cargo.toml          # Workspace manifest
```

---

## Installation

### Prerequisites

- Rust 1.70+ ([Install Rust](https://rustup.rs/))
- For web development: [Trunk](https://trunkrs.dev/) (`cargo install trunk`)

### Building from Source

```bash
# Clone the repository
git clone https://github.com/linzialessandro/Resoluto.git
cd Resoluto

# Build all components
cargo build --release

# Run tests
cargo test --workspace
```

---

## Usage

### Command Line Interface

```bash
# Generate 5 easy quadratic equations
cargo run --bin resoluto_cli -- -n 5 -d easy -t quadratic

# Generate 10 hard linear equations
cargo run --bin resoluto_cli -- -n 10 -d hard -t linear

# Generate rational equations
cargo run --bin resoluto_cli -- -n 3 -d medium -t rational

# Generate irrational equations
cargo run --bin resoluto_cli -- -n 5 -t irrational

# Generate absolute value equations
cargo run --bin resoluto_cli -- -n 5 -t absolute-value
```

**Options:**
| Flag | Description | Default |
|------|-------------|---------|
| `-n, --count <N>` | Number of problems to generate | 5 |
| `-d, --difficulty <LEVEL>` | `easy`, `medium`, or `hard` | easy |
| `-t, --problem-type <TYPE>` | `linear`, `quadratic`, `rational`, `irrational`, `absolute-value` | quadratic |

### Web Application

```bash
cd web
trunk serve --open
```

Then open your browser to `http://localhost:8080`

---

## How It Works

### Backwards Generation Algorithm

Instead of randomly generating coefficients (which often produces messy solutions), Resoluto works backwards from the desired roots:

#### Quadratic Equations (`ax² + bx + c = 0`)

1. Generate random integer roots `r₁`, `r₂`
2. Choose a scalar `a`
3. Calculate: `b = -a(r₁ + r₂)`, `c = a·r₁·r₂`
4. This ensures `(x - r₁)(x - r₂) = 0` expands correctly

#### Linear Equations (`mx + q = 0`)

1. Generate root `x`
2. Choose slope `m`
3. Calculate intercept `q = -m·x`

#### Rational Equations

Multiple templates ensure variety:
- Standard: `A/(x-p) + B/(x-q) = K`
- Linear numerator: `(Ax+B)/(x-p) = K + C/(x-q)`
- Ratio: `(Ax+B)/(Cx+D) = E/F`

#### Irrational Equations

**Easy/Medium:**
- Simple: `√(Ax+B) = C`
- Two radicals: `√(Ax+B) = √(Cx+D)`
- Linear RHS: `√(Ax+B) = Cx + D`

**Hard:**
- Double radical: `√(Ax+B) + √(Cx+D) = E`
- Triple radical: `√(Ax+B) + √(Cx+D) + √(Ex+F) = G`
- Radical difference: `√(Ax+B) - √(Cx+D) = E`
- Nested radical: `√(A√(Bx+C) + D) = E`
- Radical with linear terms: `√(Ax+B) + Cx + D = E`

#### Absolute Value Equations

- Simple: `|Ax+B| = C`
- Linear RHS: `|Ax+B| = Cx+D`
- Nested: `||Ax+B| - C| = D`
- Quadratic inside: `|x² + Bx + C| = D`

### Equation Obfuscation

To create more interesting problems, Resoluto can "obfuscate" the target polynomial by:
- Wrapping terms in algebraic identities (e.g., `(x+a)²`)
- Adding balanced terms to both sides
- Using difference of squares, product of binomials, etc.

This creates equations like `(x+2)² - 3 = x² + 8` instead of plain `4x + 1 = 0`.

---

## Development

### Running Tests

```bash
# Test all crates
cargo test --workspace

# Test with verbose output
cargo test --workspace -- --nocapture
```

### Building for Production

```bash
# Build optimized CLI
cargo build --release --bin resoluto_cli

# Build optimized web app
cd web && trunk build --release
```

The web app will be built to `web/dist/`.

---

## Deployment

The web application is automatically deployed to GitHub Pages on every push to `main`. See [.github/workflows/deploy.yml](.github/workflows/deploy.yml).

---

## License

MIT

---

## Author

Alessandro Linzi
