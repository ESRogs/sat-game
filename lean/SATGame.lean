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

/-!
# SAT Game Library

Formal verification of termination and correctness for the two-player SAT Game.

## Mathematical Foundation with Core Properties

This module imports the complete mathematical framework for formula operations:

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

### Utilities
- `Util.List`: Helper functions and lemmas for list operations

## Key Mathematical Results

1. **Termination Guarantee**: All formula operation sequences terminate in finite steps
2. **Satisfiability Preservation**: Operations preserve crucial satisfiability properties:
   - Clause removal preserves satisfiability (satisfiable formulas stay satisfiable)
   - Variable assignment preserves unsatisfiability (unsatisfiable formulas stay unsatisfiable)
   - Strategy existence for winning positions

These properties form the mathematical foundation proving that losing positions
remain losing under valid play, establishing the correctness of game outcomes.
-/
