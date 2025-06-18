import Batteries.Data.List.Basic
import Batteries.Tactic.Init
import SATGame.Boolean.Literal
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.Termination.Helpers
import SATGame.FormulaOps.Termination.Helpers.SetVariableHelpers
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.Util.List

/-!
# Set Variable Termination

Proves that variable assignment decreases literal count.

Setting x := value transforms the formula by:
1. Removing clauses satisfied by x (or ¬x)
2. Filtering x (or ¬x) from remaining clauses

Both decrease literal count since the variable appears somewhere in the formula.
-/

-- KEY HELPER: processClause never increases, and decreases for clauses with variable
theorem processClause_literal_count_behavior {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (value : Bool) :
    match processClause clause var value with
    | none => True  -- Clause removed entirely
    | some result =>
        result.length ≤ clause.length ∧
        (Clause.containsVariable clause var = true → result.length < clause.length)
    := by
  unfold processClause
  -- Case analysis: is the clause satisfied?
  by_cases h_satisfied : Clause.satisfiedBy clause var value = true
  · -- Case: clause is satisfied, maps to none
    rw [if_pos h_satisfied]
    trivial
  · -- Case: clause is not satisfied, maps to filtered clause
    rw [if_neg h_satisfied]
    simp only

    constructor
    · -- Prove: (clause.filter ...).length ≤ clause.length
      apply List.length_filter_le

    · -- Prove: Clause.containsVariable clause var = true → (clause.filter ...).length < clause.length
      intro h_contains
      -- If clause contains var, then filtering out literals with var must remove at least one
      -- Convert h_contains to existence of literal with var
      unfold Clause.containsVariable at h_contains
      rw [List.any_eq_true] at h_contains
      obtain ⟨lit, h_lit_mem, h_lit_has_var⟩ := h_contains

      -- This literal will be filtered out (since it contains the variable)
      have h_lit_not_in_filtered := literal_with_var_filtered_out clause var lit h_lit_mem h_lit_has_var

      -- Apply our general theorem about filtering removing elements
      exact filter_removes_element_strict clause (fun l => ¬(l.containsVariable var)) lit h_lit_mem h_lit_not_in_filtered

/--
Helper theorem: In nonterminal formulas, any clause containing a variable is nonempty.

This follows from the fact that nonterminal formulas have no empty clauses.
-/
theorem witness_clause_nonempty {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (clause : Clause Var) (var : Var)
    (h_nonterminal : formula.isNonterminal = true)
    (h_clause_mem : List.Mem clause formula)
    (_ : clause.containsVariable var) :
    clause.length > 0 := by
  have h_no_empty := nonterminal_implies_no_empty_clauses formula h_nonterminal
  by_contra h_not_pos
  -- h_not_pos : ¬(clause.length > 0) means clause.length ≤ 0, so clause.length = 0
  have h_zero_length : clause.length = 0 := Nat.eq_zero_of_not_pos h_not_pos
  have h_empty : clause.isEmpty := by
    rw [List.length_eq_zero_iff] at h_zero_length
    rw [h_zero_length]; rfl
  have h_formula_has_empty : formula.hasEmptyClause = true := by
    unfold Formula.hasEmptyClause; rw [List.any_eq_true]; exact ⟨clause, h_clause_mem, h_empty⟩
  rw [h_formula_has_empty] at h_no_empty; exact Bool.noConfusion h_no_empty

/--
Helper theorem: Processing clauses during variable assignment preserves non-increase property.

This encapsulates the proof that other clauses don't increase in length during processing.
-/
theorem process_clauses_nonincreasing {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool) :
    ∀ clause, List.Mem clause formula →
    ∀ result, processClause clause var value = some result →
    result.length ≤ clause.length := by
  intro clause _ result h_maps
  have h_behavior := processClause_literal_count_behavior clause var value
  rw [h_maps] at h_behavior
  exact h_behavior.1

/--
Helper theorem: When a clause is satisfied and removed, we decrease the total literal count.

This handles the case where `processClauseForVariableAssignment` returns `none`.
-/
theorem setVariable_decreases_when_clause_removed {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool)
    (witness_clause : Clause Var)
    (h_witness_mem : List.Mem witness_clause formula)
    (h_witness_removed : processClause witness_clause var value = none)
    (h_witness_nonempty : witness_clause.length > 0) :
    (formula.setVariable var value).countLiterals < formula.countLiterals := by
  unfold Formula.setVariable Formula.countLiterals
  apply List.sum_filterMap_lt_of_witness_removed
    formula (fun clause => clause.length) (processClause · var value) (fun clause => clause.length)
    witness_clause h_witness_mem h_witness_removed h_witness_nonempty
  exact process_clauses_nonincreasing formula var value

/--
Helper theorem: When a clause is shortened, we decrease the total literal count.

This handles the case where `processClause` returns a smaller clause.
-/
theorem setVariable_decreases_when_clause_shortened {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool)
    (witness_clause : Clause Var) (witness_result : Clause Var)
    (h_witness_mem : List.Mem witness_clause formula)
    (h_witness_contains : witness_clause.containsVariable var)
    (h_witness_process : processClause witness_clause var value = some witness_result) :
    (formula.setVariable var value).countLiterals < formula.countLiterals := by
  unfold Formula.setVariable Formula.countLiterals
  have h_witness_decreases : witness_result.length < witness_clause.length := by
    have h_behavior := processClause_literal_count_behavior witness_clause var value
    rw [h_witness_process] at h_behavior
    exact h_behavior.2 h_witness_contains
  apply List.sum_filterMap_lt_of_witness_decreased
    formula (fun clause => clause.length) (processClause · var value) (fun clause => clause.length)
    witness_clause h_witness_mem witness_result h_witness_process h_witness_decreases
  exact process_clauses_nonincreasing formula var value

/--
**Main Termination Theorem**: Setting a variable in a nonterminal formula decreases literal count.

This theorem establishes that variable assignment always decreases the termination measure.
The proof works by:
1. Extracting a witness clause that contains the variable
2. Showing this clause is nonempty (since the formula is nonterminal)
3. Case analysis on whether the clause is satisfied (removed) or unsatisfied (shortened)
4. In both cases, the literal count strictly decreases
-/
theorem setVariable_decreases_literalCount {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool)
    (h_nonterminal : formula.isNonterminal = true)
    (h_contains : formula.any (fun clause => clause.containsVariable var)) :
    (formula.setVariable var value).countLiterals < formula.countLiterals := by
  -- Extract witness clause containing the variable
  rw [List.any_eq_true] at h_contains
  obtain ⟨witness_clause, h_witness_mem, h_witness_contains⟩ := h_contains

  -- Witness clause is nonempty (since formula is nonterminal)
  have h_witness_nonempty := witness_clause_nonempty formula witness_clause var h_nonterminal h_witness_mem h_witness_contains

  -- Case analysis on what happens to the witness clause during processing
  cases h_witness_process : processClause witness_clause var value with
  | none =>
    -- Witness clause is satisfied and removed
    exact setVariable_decreases_when_clause_removed formula var value
      witness_clause h_witness_mem h_witness_process h_witness_nonempty
  | some witness_result =>
    -- Witness clause is shortened but not removed
    exact setVariable_decreases_when_clause_shortened formula var value
      witness_clause witness_result h_witness_mem h_witness_contains h_witness_process
