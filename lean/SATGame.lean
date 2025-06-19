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

Formal verification of termination and correctness for the two-player SAT Game.

## Mathematical Foundation with Termination Proofs

This module imports the core mathematical framework and termination verification:

### Boolean Logic Foundation
- `Boolean.Literal`: Literals with variables and boolean values
- `CNF.Clause`: Disjunctions of literals
- `CNF.Formula`: Conjunctions of clauses (CNF formulas)
- `CNF.Satisfiability`: Satisfiability definitions and properties

### Formula Operations Framework
- `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
- `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
- `FormulaOps.ValidSequences`: Valid sequences of operations

### Termination Proofs
- `FormulaOps.Termination.Main`: Master termination theorem and well-foundedness
- `FormulaOps.Termination.SetVariable`: Termination proofs for variable assignment
- `FormulaOps.Termination.RemoveClause`: Termination proofs for clause removal
- `FormulaOps.Termination.Nonterminal`: Properties of nonterminal formulas
- `FormulaOps.Termination.Helpers`: Supporting lemmas and utilities

### Utilities
- `Util.List`: Helper functions and lemmas for list operations

## Key Result: Termination Guarantee

**Theorem**: All formula operation sequences terminate in finite steps.

This is proven using the literal count as a termination measure - every valid
operation strictly decreases the total number of literals in the formula,
ensuring no infinite game sequences are possible.
-/
