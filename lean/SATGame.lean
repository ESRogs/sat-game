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

/-!
# SAT Game Library

Core mathematical types for Boolean satisfiability and CNF formulas with strategic game infrastructure.

## Components
- **Boolean Logic**: Literals, clauses, formulas, and satisfiability
- **Formula Operations**: Variable assignment, clause removal, termination proofs, and satisfiability preservation
- **Game Infrastructure**: Players, strategies, winning conditions, and game execution
- **Utilities**: List helpers and lemmas

## Key Results
1. **Termination**: All formula operation sequences terminate in finite steps
2. **Satisfiability Preservation**: Operations preserve key satisfiability properties
3. **Strategic Framework**: Foundation for proving correctness under perfect play
-/
