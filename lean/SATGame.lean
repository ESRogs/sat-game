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

Core mathematical types for Boolean satisfiability and CNF formulas.

## Infrastructure
- **Boolean Logic**: Literals, clauses, formulas, and satisfiability
- **Formula Operations**: Variable assignment, clause removal, and operation sequences
- **Game Framework**: Strategic game concepts, players, and winning conditions
- **Utilities**: List helpers and lemmas

## Proofs
- **Termination**: Sequences of formula operations are guaranteed to terminate
- **Satisfiability Preservation**:
  - `setVariable` preserves unsatisfiability
  - `removeClause` preserves satisfiability
- **Strategic Correctness**: Losing positions remain losing under valid play
-/
