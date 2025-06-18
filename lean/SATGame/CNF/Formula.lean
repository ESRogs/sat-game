import SATGame.CNF.Clause

/-!
# CNF Formulas

Defines formulas as conjunctions (AND) of clauses.

A CNF formula is a list of clauses representing their conjunction.
Provides predicates for checking variable containment, empty clauses, and fundamental properties.
-/

/-- A CNF formula is a conjunction (AND) of clauses -/
def Formula (Var : Type) := List (Clause Var)

/-- Check if any clause in the formula contains the given variable -/
def Formula.containsVariable {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) : Bool :=
  formula.any (fun clause => clause.containsVariable var)

/-- If any clause in a formula contains a variable, then the formula contains that variable -/
theorem clause_var_implies_formula_var {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) :
    (∃ clause, List.Mem clause formula ∧ clause.containsVariable var = true) → formula.containsVariable var = true := by
  intro ⟨clause, h_clause_in, h_clause_contains⟩
  unfold Formula.containsVariable
  rw [List.any_eq_true]
  exact ⟨clause, h_clause_in, h_clause_contains⟩

/-- Check if the formula contains any empty clause, making it unsatisfiable -/
def Formula.hasEmptyClause {Var : Type} (formula : Formula Var) : Bool :=
  formula.any (fun clause => clause.isEmpty)
