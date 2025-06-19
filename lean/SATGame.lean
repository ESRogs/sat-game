import SATGame.Boolean.Literal
import SATGame.CNF.Clause
import SATGame.CNF.Formula
import SATGame.CNF.Satisfiability
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.ValidSequences
import SATGame.Util.List

/-!
# SAT Game Library

Core mathematical types for Boolean satisfiability and formula operations.

## Core Modules

### Mathematical Foundation
- `Boolean/`, `CNF/`: Basic types for literals, clauses, formulas, and satisfiability
- `FormulaOps/`: Formula operation framework
  - `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
  - `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
  - `FormulaOps.ValidSequences`: Valid sequences of operations
- `Util/`: Helper functions and lemmas for list operations

These components provide the mathematical foundation for formula operations.
-/
