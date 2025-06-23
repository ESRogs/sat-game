import SATGame.Boolean.Literal
import SATGame.CNF.Clause
import SATGame.CNF.Formula
import SATGame.CNF.Satisfiability
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.SatisfiabilityPreservation
import SATGame.Game.Basic
import SATGame.Game.Correctness.StrategyExistence
import SATGame.Game.Correctness.AffirmativeAdvantage
import SATGame.Game.Correctness.PositionEvaluation
import SATGame.FormulaOps.Termination.Helpers
import SATGame.FormulaOps.Termination.Helpers.SetVariableHelpers
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.FormulaOps.Termination.RemoveClause
import SATGame.FormulaOps.Termination.SetVariable
import SATGame.FormulaOps.Termination.Main
import SATGame.Examples

/-!
# SAT Game Library

Formal verification of termination and correctness for the two-player SAT Game.

## Current Results

### Mathematical Foundations (FormulaOps)
- **Termination**: Formula operation sequences always terminate (see `FormulaOps/Termination/Main`)
- **Preservation Properties**: Mathematical preservation of satisfiability under operations (see `FormulaOps/SatisfiabilityPreservation.lean`)
- **Nonterminal Properties**: Fundamental properties of formulas where operations can continue (see `FormulaOps/Termination/Nonterminal.lean`)

### Game Theory (Game)
- **Strategy Existence**: Players with winning positions have preserving moves (see `Game/Correctness/StrategyExistence.lean`)
- **Position Evaluation**: Losing positions remain losing under valid play (see `Game/Correctness/PositionEvaluation.lean`)
- **Affirmative Advantage**: Affirmative can win from any satisfiable formula (see `Game/Correctness/AffirmativeAdvantage.lean`)

## Development Roadmap
See `ROADMAP.md` for the complete strategy toward proving "the right side wins under perfect play."

## Core Modules

### Mathematical Foundation
- `Boolean/`, `CNF/`: Basic types for literals, clauses, formulas, and satisfiability
- `FormulaOps/`: Formula operation sequences and their mathematical properties
  - `FormulaOps.FormulaOps`: Variable assignment and clause removal operations
  - `FormulaOps.Termination/`: Proofs that operation sequences terminate
  - `FormulaOps.SatisfiabilityPreservation`: Mathematical preservation properties

### Game Layer
- `Game/`: Strategic game concepts built on formula operations
  - `Game.Basic`: Players, winning conditions, and round structures
  - `Game.Correctness/`: Game-theoretic interpretations and strategic analysis

### Examples and Verification
- `Examples`: Demonstrations of formula operations and game sequences
-/
