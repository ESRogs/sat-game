import SATGame.Boolean.Literal

/-!
# CNF Clauses

Defines clauses as disjunctions (OR) of literals.

A clause is a list of literals representing their disjunction.
Empty clauses are unsatisfiable; non-empty clauses contribute to the literal count.
Provides containment checks and fundamental properties.
-/

/-- A clause is a disjunction (OR) of literals -/
def Clause (Var : Type) := List (Literal Var)

/-- Check if the clause is empty (contains no literals) -/
def Clause.isEmpty {Var : Type} (clause : Clause Var) : Bool :=
  List.isEmpty clause

/-- Check if the clause contains any literal with the given variable -/
def Clause.containsVariable {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) : Bool :=
  clause.any (fun lit => lit.containsVariable var)

/-- If any literal in a clause contains a variable, then the clause contains that variable -/
theorem literal_var_implies_clause_var {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) :
    (∃ lit, List.Mem lit clause ∧ lit.containsVariable var = true) → clause.containsVariable var = true := by
  intro ⟨lit, h_lit_in, h_lit_contains⟩
  unfold Clause.containsVariable
  rw [List.any_eq_true]
  exact ⟨lit, h_lit_in, h_lit_contains⟩

/-- Check if assigning a specific variable to a value would be sufficient to satisfy this clause.
    Returns true if the clause contains a literal with that variable that would be satisfied by the assignment. -/
def Clause.satisfiedBy {Var : Type} [DecidableEq Var] (clause : Clause Var) (var : Var) (value : Bool) : Bool :=
  clause.any fun lit => lit.containsVariable var && lit.eval value
