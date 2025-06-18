import SATGame.CNF.Formula
import SATGame.CNF.Clause
import SATGame.Boolean.Literal

/-!
# Satisfiability for CNF Formulas

Defines what it means for a CNF formula to be satisfiable.

A formula is satisfiable if there exists an assignment of boolean values to variables
such that every clause in the formula evaluates to true.
-/

/-- An assignment maps variables to boolean values -/
def Assignment (Var : Type) := Var → Bool

/-- Check if a literal is satisfied by an assignment -/
def Literal.satisfiedByAssignment {Var : Type} [DecidableEq Var] (lit : Literal Var) (α : Assignment Var) : Bool :=
  match lit with
  | Literal.pos v => α v
  | Literal.neg v => !(α v)

/-- Check if a clause is satisfied by an assignment -/
def Clause.satisfiedByAssignment {Var : Type} [DecidableEq Var] (clause : Clause Var) (α : Assignment Var) : Bool :=
  clause.any (fun lit => lit.satisfiedByAssignment α)

/-- Check if a formula is satisfied by an assignment -/
def Formula.satisfiedByAssignment {Var : Type} [DecidableEq Var] (formula : Formula Var) (α : Assignment Var) : Bool :=
  formula.all (fun clause => clause.satisfiedByAssignment α)

/-- A formula is satisfiable if there exists some assignment that satisfies it -/
def Formula.IsSatisfiable {Var : Type} [DecidableEq Var] (formula : Formula Var) : Prop :=
  ∃ α : Assignment Var, formula.satisfiedByAssignment α = true

/-!
## Basic Properties
-/

/--
A formula is a minimal unsatisfiable core if it's unsatisfiable and removing any clause makes it satisfiable.

This captures the notion that every clause is essential for the unsatisfiability.
-/
def Formula.IsMinimalUnsatisfiableCore {Var : Type} [DecidableEq Var] (formula : Formula Var) : Prop :=
  ¬(Formula.IsSatisfiable formula) ∧
  ∀ (index : Nat), index < formula.length → Formula.IsSatisfiable (formula.eraseIdx index)

/-- Empty formula is satisfiable -/
theorem empty_formula_satisfiable {Var : Type} [DecidableEq Var] :
    Formula.IsSatisfiable ([] : Formula Var) :=
  ⟨fun _ => true, rfl⟩

/-- Formulas containing empty clauses are unsatisfiable -/
theorem formula_with_empty_clause_unsatisfiable {Var : Type} [DecidableEq Var] (formula : Formula Var)
    (h_has_empty : formula.hasEmptyClause = true) :
    ¬formula.IsSatisfiable := by
  intro ⟨assignment, h_satisfies⟩
  -- Extract the empty clause
  unfold Formula.hasEmptyClause at h_has_empty
  rw [List.any_eq_true] at h_has_empty
  obtain ⟨empty_clause, h_in_formula, h_isEmpty⟩ := h_has_empty
  -- The assignment must satisfy all clauses
  unfold Formula.satisfiedByAssignment at h_satisfies
  rw [List.all_eq_true] at h_satisfies
  have h_empty_satisfied := h_satisfies empty_clause h_in_formula
  -- But empty clauses cannot be satisfied
  unfold Clause.satisfiedByAssignment at h_empty_satisfied
  unfold Clause.isEmpty at h_isEmpty
  rw [List.isEmpty_iff] at h_isEmpty
  rw [h_isEmpty] at h_empty_satisfied
  simp at h_empty_satisfied

/-- Extending assignment to fix a variable preserves literal satisfaction for unrelated literals -/
theorem assignment_extension_preserves_unrelated_literals {Var : Type} [DecidableEq Var]
    (lit : Literal Var) (α : Assignment Var) (var : Var) (value : Bool) :
    ¬(lit.containsVariable var) →
    lit.satisfiedByAssignment α = lit.satisfiedByAssignment (fun v => if v = var then value else α v) := by
  intro h_unrelated
  unfold Literal.satisfiedByAssignment
  cases lit with
  | pos v =>
    unfold Literal.containsVariable Literal.getVariable at h_unrelated
    simp at h_unrelated
    simp [h_unrelated]
  | neg v =>
    unfold Literal.containsVariable Literal.getVariable at h_unrelated
    simp at h_unrelated
    simp [h_unrelated]

