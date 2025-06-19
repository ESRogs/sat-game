import SATGame.Boolean.Literal
import SATGame.CNF.Clause
import SATGame.CNF.Formula
import SATGame.CNF.Satisfiability
import SATGame.Util.List
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.ValidSequences

/-!
# SAT Game Library

Formal verification of termination and correctness for the two-player SAT Game.

## Core Mathematical Types

This module imports the fundamental mathematical types for the SAT Game:

### Boolean Logic Foundation
- `Boolean.Literal`: Literals with variables and boolean values
- `CNF.Clause`: Disjunctions of literals
- `CNF.Formula`: Conjunctions of clauses (CNF formulas)
- `CNF.Satisfiability`: Satisfiability definitions and properties

### Formula Operations Framework
- `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
- `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
- `FormulaOps.ValidSequences`: Valid sequences of operations

### Utilities
- `Util.List`: Helper functions and lemmas for list operations

These components provide the mathematical foundation for formula operations and game logic.
-/
