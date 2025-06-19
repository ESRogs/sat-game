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

Mathematical foundations for Boolean satisfiability with termination verification.

## Current Results

### Mathematical Foundations (FormulaOps)
- **Termination**: Formula operation sequences always terminate (see `FormulaOps/Termination/Main`)
- **Nonterminal Properties**: Fundamental properties of formulas where operations can continue (see `FormulaOps/Termination/Nonterminal.lean`)

## Core Modules

### Mathematical Foundation
- `Boolean/`, `CNF/`: Basic types for literals, clauses, formulas, and satisfiability
- `FormulaOps/`: Formula operation sequences and their mathematical properties
  - `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
  - `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
  - `FormulaOps.ValidSequences`: Valid sequences of operations
  - `FormulaOps.Termination/`: Proofs that operation sequences terminate

### Utilities
- `Util/`: Helper functions and lemmas for list operations
-/
