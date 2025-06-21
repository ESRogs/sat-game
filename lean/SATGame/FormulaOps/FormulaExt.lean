import SATGame.CNF.Formula

/-!
# Formula Operations

Operations that transform CNF formulas through variable assignment and clause removal.
Includes predicates for formula states and termination metrics.
-/


/-- Process clause when setting variable: remove if satisfied, else filter literals -/
def processClause {Var : Type} [DecidableEq Var] (clause : Clause Var) (var : Var) (value : Bool) : Option (Clause Var) :=
  if clause.satisfiedBy var value then
    none
  else
    some (clause.filter fun lit => ¬(lit.containsVariable var))

/-- Set a variable to a value and simplify the formula accordingly -/
def Formula.setVariable {Var : Type} [DecidableEq Var] (formula : Formula Var) (var : Var) (value : Bool) : Formula Var :=
  formula.filterMap (processClause · var value)

/-- Remove the clause at the given index from the formula -/
def Formula.removeClause {Var : Type} (formula : Formula Var) (index : Nat) : Formula Var :=
  formula.eraseIdx index

/-- Terminal formula: satisfiability is trivially determined (empty or has empty clause) -/
def Formula.isTerminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isEmpty || formula.hasEmptyClause

/-- Nonterminal formula: operations can continue (not terminal) -/
def Formula.isNonterminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isTerminal = false

/-- Count total literals across all clauses (termination measure) -/
def Formula.countLiterals {Var : Type} (formula : Formula Var) : Nat :=
  formula.map (fun clause => clause.length) |>.sum

/-- Terminal formulas are either empty or contain an empty clause -/
theorem terminal_formula_classification {Var : Type} (formula : Formula Var)
    (h_terminal : formula.isTerminal = true) :
    formula = [] ∨ formula.hasEmptyClause := by
  unfold Formula.isTerminal at h_terminal
  simp at h_terminal
  exact h_terminal
