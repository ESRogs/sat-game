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

Core mathematical types for Boolean satisfiability and CNF formulas.

## Complete Mathematical Framework with Game Infrastructure

This module imports the full mathematical foundation plus game-theoretic concepts:

### Boolean Logic Foundation
- `Boolean.Literal`: Positive/negative variable literals
- `CNF.Clause`: Disjunctions of literals
- `CNF.Formula`: Conjunctions of clauses
- `CNF.Satisfiability`: Satisfiability definitions and theorems

### Formula Operations Framework
- `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
- `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
- `FormulaOps.ValidSequences`: Valid sequences of operations

### Formula Operations Framework
- `FormulaOps.FormulaExt`: Extended formula properties (terminal predicates, literal counts)
- `FormulaOps.FormulaOps`: Core operations (setVariable, removeClause)
- `FormulaOps.ValidSequences`: Valid sequences of operations

### Mathematical Properties
- `FormulaOps.Termination.*`: Complete termination proofs (all games end)
- `FormulaOps.SatisfiabilityPreservation`: Preservation properties under operations

### Game Infrastructure
- `Game.Basic`: Strategic game concepts built on formula operations
  - Players (Affirmative seeks satisfiability, Negative seeks unsatisfiability)
  - Strategies and winning conditions
  - Game execution with AffirmativeStrategy type
  - Round structures and valid game sequences

### Utilities
- `Util.List`: Helper functions and lemmas for list operations

## Key Mathematical Results

1. **Termination Guarantee**: All formula operation sequences terminate in finite steps
2. **Satisfiability Preservation**: Operations preserve crucial satisfiability properties
3. **Game Infrastructure**: Strategic framework connecting formula operations to game play

The combination of mathematical properties and game infrastructure provides the
foundation for proving strategic correctness - that the right side wins under
perfect play in the SAT Game.
-/
