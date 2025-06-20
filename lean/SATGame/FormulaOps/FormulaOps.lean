import SATGame.FormulaOps.FormulaExt

/-!
# Formula Operations

Defines the FormulaOp type for formula transformations (SetVariable, RemoveClause).
-/

/-- Formula transformation operations -/
inductive FormulaOp (Var : Type) where
  | SetVariable : Var → Bool → FormulaOp Var  -- Set variable (with automatic simplification)
  | RemoveClause : Nat → FormulaOp Var        -- Remove clause by index

/-- Check if a formula operation can be legally applied to a given formula -/
def FormulaOp.IsApplicable {Var : Type} [DecidableEq Var]
    (op : FormulaOp Var) (formula : Formula Var) : Prop :=
  match op with
  | FormulaOp.SetVariable var _ => formula.containsVariable var
  | FormulaOp.RemoveClause index => index < formula.length

/-- Apply a formula operation to transform the formula -/
def Formula.applyOp {Var : Type} [DecidableEq Var] (formula : Formula Var) (op : FormulaOp Var) : Formula Var :=
  match op with
  | FormulaOp.SetVariable var value => formula.setVariable var value
  | FormulaOp.RemoveClause index => formula.removeClause index
