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

/-!
# SAT Game Library

Core mathematical types for Boolean satisfiability and CNF formulas.

## Components
- **Boolean Logic**: Literals, clauses, formulas, and satisfiability
- **Formula Operations**: Variable assignment, clause removal, and operation sequences
- **Termination**: Proofs that formula operation sequences terminate
- **Utilities**: List helpers and lemmas
-/
