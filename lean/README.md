# SAT Game Formal Verification

This directory contains formal verification in Lean 4 of the SAT Game mechanics and properties.

## 🎯 **Major Achievement: Termination Proof Complete!**

We have formally proven that the SAT Game terminates for all possible game sequences. This is a foundational result that guarantees:

- Every game reaches a definitive outcome
- No infinite games are possible
- Future strategic analysis can rely on finite game trees

## Project Structure

- **`SATGame/Boolean/`** - Boolean logic types and literal definitions
- **`SATGame/CNF/`** - CNF formula and clause representations
- **`SATGame/Correctness/`** - **Fairness properties** proving game operations are fair
- **`SATGame/Termination/`** - **Termination proofs** (the main theoretical contribution)
- **`SATGame/Examples.lean`** - Worked examples and verification tests
- **`SATGame/FormulaOps.lean`** - Game operations and formula transformations
- **`SATGame/Util/`** - Utility functions and list operations

## Development Standards

### Lean Naming Conventions
This project follows the [Lean Community naming conventions](https://leanprover-community.github.io/contribute/naming.html):
- **Theorems/propositions**: `snake_case` (e.g., `setVariable_preserves_unsatisfiability`)
- **Types/classes**: `UpperCamelCase` (e.g., `Formula`, `Assignment`)  
- **Functions**: Named like their return values
- **Other terms**: `lowerCamelCase`
- **Descriptive names**: Use "of" to separate hypotheses, prefer descriptive prefixes
- **Preservation properties**: Use `preserves` or similar descriptive verbs
- **Hypothesis names**: We use descriptive `h_snake_case` names (e.g., `h_satisfied`, `h_process`). This follows the convention that terms of Props use snake_case, since hypotheses are proof terms of type Prop
- **Theorem vs Lemma**: Always use `theorem` keyword, never `lemma`, for consistency across the codebase

### Code Organization
- **Functional style**: Prefer functional programming patterns
- **Newline endings**: All files should end with newlines
- **Logical ordering**: Theorems should appear in logical dependency order
- **Helper theorems**: Place before main theorems that use them
- **Clear documentation**: Include docstrings explaining module purpose and proof strategies
- **Helper functions**: Add simple computational helper functions (like `getVariable` for `Literal`) when they make proofs cleaner and more direct. Prefer extracting concrete values over existential proofs when possible
- **Refactoring caution**: When refactoring existing definitions to use helper functions, be aware that semantic differences can break existing proofs. Pattern matching and helper function compositions may behave differently in proof contexts, even when they're logically equivalent

### Commit Standards
- **Build requirement**: Every commit must build successfully (`lake build`)
- **Format requirement**: Run `scripts/format.sh` before committing
- **Atomic commits**: Each commit should be self-contained and focused
- **Commit messages**: Follow conventional commit format (feat:, fix:, refactor:, etc.)

### Style Checking
Currently, style adherence is checked manually during code review. Lean 4 provides some built-in linting, but comprehensive naming convention checking requires manual verification against the [community guidelines](https://leanprover-community.github.io/contribute/naming.html).

## Building

```bash
# Build all proofs
lake build
```

## Key Theorems Proven

- **Game Termination**: All game sequences terminate in finite steps
- **Move Validity**: All game operations preserve formula structure
- **Terminal State Recognition**: Decidable winning conditions

The termination proof uses a lexicographic ordering on formula structure, proving that each valid move strictly decreases a well-founded measure.

## Dependencies

- Lean 4 (v4.20.0)
- Mathlib v4.20.0

This formal verification provides the mathematical foundation for implementing SAT Game solvers and strategic analysis tools.