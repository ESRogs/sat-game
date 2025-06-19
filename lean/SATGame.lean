import SATGame.Boolean.Literal
import SATGame.CNF.Clause
import SATGame.CNF.Formula
import SATGame.CNF.Satisfiability
import SATGame.Util.List
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.ValidSequences
import SATGame.FormulaOps.Termination.Main
import SATGame.FormulaOps.Termination.SetVariable
import SATGame.FormulaOps.Termination.RemoveClause
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.FormulaOps.Termination.Helpers
import SATGame.FormulaOps.Termination.Helpers.SetVariableHelpers
import SATGame.FormulaOps.SatisfiabilityPreservation
import SATGame.Game.Basic
import SATGame.Game.Correctness.StrategyExistence
import SATGame.Game.Correctness.PositionEvaluation

/-!
# SAT Game Library

Formal verification of termination and correctness for the two-player SAT Game.

## Complete Framework with Game Correctness Properties

This module imports the full mathematical foundation plus strategic correctness proofs:

### Boolean Logic Foundation
- `Boolean.Literal`: Literals with variables and boolean values
- `CNF.Clause`: Disjunctions of literals
- `CNF.Formula`: Conjunctions of clauses (CNF formulas)
- `CNF.Satisfiability`: Satisfiability definitions and properties

### Formula Operations Framework
- `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
- `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
- `FormulaOps.ValidSequences`: Valid sequences of operations

### Mathematical Properties
- `FormulaOps.Termination.*`: Complete termination proofs (all games end)
- `FormulaOps.SatisfiabilityPreservation`: Preservation properties under operations

### Game Infrastructure
- `Game.Basic`: Strategic game concepts built on formula operations

### Strategic Correctness
- `Game.Correctness.StrategyExistence`: Players with winning positions have preserving moves
- `Game.Correctness.PositionEvaluation`: Losing positions remain losing under valid play

### Utilities
- `Util.List`: Helper functions and lemmas for list operations

## Key Results: Strategic Correctness Foundation

1. **Termination Guarantee**: All formula operation sequences terminate in finite steps
2. **Satisfiability Preservation**: Operations preserve crucial satisfiability properties
3. **Strategy Existence**: Players in winning positions always have moves that preserve their advantage
4. **Position Stability**: Players in losing positions cannot escape through any valid moves

These properties establish the mathematical foundation for game correctness:
losing positions remain losing, winning positions can be preserved, ensuring
that initial position determines outcome under perfect play.
-/
