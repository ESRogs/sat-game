import SATGame.CNF.Formula

/-!
# Formula Operations

Operations that transform CNF formulas through variable assignment and clause removal.
Includes predicates for formula states and termination metrics.
-/


/-- Process a single clause during variable assignment:
    remove satisfied clauses, filter literals from unsatisfied clauses -/
def processClauseForVariableAssignment {Var : Type} [DecidableEq Var] (clause : Clause Var) (var : Var) (value : Bool) : Option (Clause Var) :=
  if clause.satisfiedBy var value then
    none  -- Remove satisfied clauses
  else
    -- Remove all literals containing the variable from the clause
    -- Since the clause isn't satisfied, none of these literals can be true
    some (clause.filter fun lit => ¬(lit.containsVariable var))

/-- Set a variable to a value and simplify the formula accordingly -/
def Formula.setVariable {Var : Type} [DecidableEq Var] (formula : Formula Var) (var : Var) (value : Bool) : Formula Var :=
  formula.filterMap (processClauseForVariableAssignment · var value)

/-- Remove the clause at the given index from the formula -/
def Formula.removeClause {Var : Type} (formula : Formula Var) (index : Nat) : Formula Var :=
  formula.eraseIdx index

/--
A formula is terminal when either all clauses are satisfied (empty formula)
or an empty clause exists (unsatisfiable).
-/
def Formula.isTerminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isEmpty || formula.hasEmptyClause

/-- A formula is nonterminal when it has at least one clause, and none of its clauses are empty -/
def Formula.isNonterminal {Var : Type} (formula : Formula Var) : Bool :=
  formula.isTerminal = false

/-- Count total literals across all clauses (termination measure) -/
def Formula.countLiterals {Var : Type} (formula : Formula Var) : Nat :=
  formula.map (fun clause => clause.length) |>.sum

/--
Terminal formulas are either empty (trivially satisfiable) or contain
an empty clause (trivially unsatisfiable).
-/
theorem terminal_formula_classification {Var : Type} (formula : Formula Var)
    (h_terminal : formula.isTerminal = true) :
    formula = [] ∨ formula.hasEmptyClause := by
  unfold Formula.isTerminal at h_terminal
  simp at h_terminal
  exact h_terminal
