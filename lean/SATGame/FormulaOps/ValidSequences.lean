import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps

/-!
# Valid Operation Sequences

This module defines inductive types for valid sequences of formula operations.
These ensure that operations are checked for validity at each step of application.
-/

/-- Check if a sequence of clause removal operations is valid when applied step-by-step -/
inductive valid_clause_removal_sequence {Var : Type} [DecidableEq Var] : Formula Var → List (FormulaOp Var) → Prop where
  | nil : ∀ {formula}, valid_clause_removal_sequence formula []
  | cons : ∀ {formula op rest},
           formula.isNonterminal = true →
           (∃ index, op = FormulaOp.RemoveClause index) →
           op.IsApplicable formula →
           valid_clause_removal_sequence (formula.applyOp op) rest →
           valid_clause_removal_sequence formula (op :: rest)

/-- Check if a sequence of variable assignment operations is valid when applied step-by-step -/
inductive valid_variable_assignment_sequence {Var : Type} [DecidableEq Var] : Formula Var → List (FormulaOp Var) → Prop where
  | nil : ∀ {formula}, valid_variable_assignment_sequence formula []
  | cons : ∀ {formula op rest},
           formula.isNonterminal = true →
           (∃ var value, op = FormulaOp.SetVariable var value) →
           op.IsApplicable formula →
           valid_variable_assignment_sequence (formula.applyOp op) rest →
           valid_variable_assignment_sequence formula (op :: rest)

/-- All operations in a valid clause removal sequence are RemoveClause operations -/
theorem valid_clause_removal_sequence_all_removes {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var))
    (h_valid : valid_clause_removal_sequence formula ops) :
    ∀ op ∈ ops, ∃ index, op = FormulaOp.RemoveClause index := by
  induction h_valid with
  | nil =>
    intros op h_mem
    simp at h_mem
  | cons _ h_is_remove _ _ ih =>
    intros op h_mem
    simp at h_mem
    cases h_mem with
    | inl h_eq =>
      subst h_eq
      exact h_is_remove
    | inr h_in_rest =>
      exact ih op h_in_rest
