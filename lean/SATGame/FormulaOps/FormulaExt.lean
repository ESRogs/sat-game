import SATGame.CNF.Formula

/-!
# Formula Operations

This module defines operations that transform CNF formulas through variable assignment
and clause removal, along with predicates for formula states and metrics.

## Main Operations

1. **Variable Assignment**: `Formula.setVariable` - assign true/false to a variable
2. **Clause Removal**: `Formula.removeClause` - remove a clause by index
3. **State Predicates**: `isTerminal`, `isNonterminal` - check if operations can continue
4. **Metrics**: `countLiterals` - termination measure for operation sequences
-/


/-- Process a single clause during variable assignment:
    remove satisfied clauses, filter literals from unsatisfied clauses -/
def processClauseForVariableAssignment {Var : Type} [DecidableEq Var] (clause : Clause Var) (var : Var) (value : Bool) : Option (Clause Var) :=
  if clause.satisfiedBy var value then
    none  -- Remove satisfied clauses
  else
    -- Remove all literals containing the variable from the clause
    -- Since the clause isn't satisfied, none of these literals can be true
    let simplified := clause.filter fun lit => ¬(lit.containsVariable var)
    some simplified

/-- Set a variable to a value and simplify the formula accordingly -/
def Formula.setVariable {Var : Type} [DecidableEq Var] (formula : Formula Var) (var : Var) (value : Bool) : Formula Var :=
  formula.filterMap (processClauseForVariableAssignment · var value)

/-- Remove the clause at the given index from the formula -/
def Formula.removeClause {Var : Type} (formula : Formula Var) (index : Nat) : Formula Var :=
  formula.eraseIdx index

/-!
## Formula States
-/

/--
Terminal formula: satisfiability is trivially determined.

A formula is terminal when either all clauses are satisfied (empty formula)
or an empty clause exists (unsatisfiable).
-/
def Formula.isTerminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isEmpty || formula.hasEmptyClause

/--
Nonterminal formula: operations can continue.

A formula is nonterminal when it's neither empty nor contains an empty clause,
meaning further operations can be applied.
-/
def Formula.isNonterminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isTerminal = false

/-!
## Logical Predicates (Props)
-/

/--
Terminal formula (Prop version): satisfiability is trivially determined.

This is the logical/theorem version of `isTerminal` for cleaner reasoning
in theorem parameters and hypotheses.
-/
def Formula.IsTerminal {Var : Type} (formula : Formula Var) : Prop :=
  formula.isTerminal

/--
Nonterminal formula (Prop version): operations can continue.

This is the logical/theorem version of `isNonterminal` for cleaner reasoning
in theorem parameters and hypotheses.
-/
def Formula.IsNonterminal {Var : Type} (formula : Formula Var) : Prop :=
  ¬formula.IsTerminal

/-!
## Conversion Lemmas
-/

/-- Conversion between Bool and Prop versions of isTerminal -/
theorem isTerminal_iff_IsTerminal {Var : Type} (formula : Formula Var) :
  formula.isTerminal = true ↔ Formula.IsTerminal formula := by
  unfold Formula.IsTerminal
  simp

/-- Conversion between Bool and Prop versions of isNonterminal -/
theorem isNonterminal_iff_IsNonterminal {Var : Type} (formula : Formula Var) :
  formula.isNonterminal = true ↔ Formula.IsNonterminal formula := by
  unfold Formula.IsNonterminal Formula.IsTerminal
  simp [Formula.isNonterminal]

/-- IsNonterminal is equivalent to not IsTerminal -/
theorem IsNonterminal_iff_not_IsTerminal {Var : Type} (formula : Formula Var) :
  Formula.IsNonterminal formula ↔ ¬Formula.IsTerminal formula := by
  rfl

/-!
## Termination Measure
-/

/--
Count literals: the termination measure for formula operations.

This function counts the total number of literals across all clauses. Every valid
operation on a nonterminal formula strictly decreases this count, providing
the well-founded measure needed to prove termination.
-/
def Formula.countLiterals {Var : Type} (formula : Formula Var) : Nat :=
  formula.map (fun clause => clause.length) |>.sum

/-!
## Terminal Formula Properties
-/

/--
Terminal formulas have deterministic satisfiability status.

Every terminal formula is either empty (trivially satisfiable) or contains
an empty clause (trivially unsatisfiable). This mathematical classification
is fundamental to understanding when formula operations must cease.
-/
theorem terminal_formula_classification {Var : Type} (formula : Formula Var)
    (h_terminal : formula.isTerminal = true) :
    formula = [] ∨ formula.hasEmptyClause := by
  -- Terminal formulas are either empty or have empty clauses
  unfold Formula.isTerminal at h_terminal
  simp at h_terminal
  exact h_terminal
