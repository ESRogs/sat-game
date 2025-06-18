/-!
# Boolean Literals

Defines positive and negative variable literals for CNF formulas.

A literal is either a positive variable `x` or its negation `¬x`.
Provides evaluation functions, variable containment checks, and fundamental properties.
-/

/-- A literal is either a positive or negative variable -/
inductive Literal (Var : Type) where
  | pos : Var → Literal Var  -- positive literal (e.g., x)
  | neg : Var → Literal Var  -- negative literal (e.g., ¬x)
  deriving DecidableEq

/-- Evaluate a literal under a boolean assignment to its variable -/
def Literal.eval {Var : Type} (lit : Literal Var) (value : Bool) : Bool :=
  match lit with
  | Literal.pos _ => value     -- positive literal x is true when x := true
  | Literal.neg _ => !value    -- negative literal ¬x is true when x := false

/-- Extract the variable from a literal -/
def Literal.getVariable {Var : Type} (lit : Literal Var) : Var :=
  match lit with
  | Literal.pos v => v
  | Literal.neg v => v

/-- Check if a literal contains a specific variable (either positive or negative) -/
def Literal.containsVariable {Var : Type} [DecidableEq Var] (lit : Literal Var) (var : Var) : Bool :=
  decide (lit.getVariable = var)

/-- Check if a literal becomes true when a specific variable is assigned a value -/
def Literal.becomesTrueUnder {Var : Type} [DecidableEq Var] (lit : Literal Var) (var : Var) (value : Bool) : Bool :=
  lit.containsVariable var && lit.eval value

/-- A literal always contains its own variable -/
theorem Literal.contains_own_variable {Var : Type} [DecidableEq Var] (lit : Literal Var) :
    lit.containsVariable lit.getVariable = true := by
  unfold containsVariable getVariable
  simp

/-- Every literal contains at least one variable (namely, its own) -/
theorem literal_contains_variable {Var : Type} [DecidableEq Var] (literal : Literal Var) :
    ∃ var, literal.containsVariable var = true := by
  exact ⟨literal.getVariable, literal.contains_own_variable⟩
