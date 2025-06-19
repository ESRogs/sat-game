import SATGame.FormulaOps.FormulaExt

/-!
# Termination Helpers

Basic utilities for termination proofs.

This module contains:
- Helper functions for literal and clause operations
- Basic case analysis helpers
- Simple utility theorems
-/

-- Helper: Simple case analysis for setVariable outcomes
theorem setVariable_case_analysis {Var : Type} [DecidableEq Var] (clause : Clause Var) (var : Var) (value : Bool) :
    (clause.any (fun lit => match lit with
      | Literal.pos v => v = var && value
      | Literal.neg v => v = var && !value)) ∨
    ¬(clause.any (fun lit => match lit with
      | Literal.pos v => v = var && value
      | Literal.neg v => v = var && !value)) := by
  by_cases hSatisfied : clause.any (fun lit => match lit with
    | Literal.pos v => v = var && value
    | Literal.neg v => v = var && !value)
  · left; exact hSatisfied
  · right; exact hSatisfied

