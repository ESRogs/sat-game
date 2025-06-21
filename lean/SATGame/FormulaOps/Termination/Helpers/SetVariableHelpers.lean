import Mathlib.Data.List.Basic
import SATGame.Boolean.Literal
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.Util.List

/-!
# Set Variable Helper Functions

Complex utility theorems for variable assignment termination proofs.

This module contains complex helper functions extracted from SetVariable.lean
to improve code organization and readability.

These helpers support the main termination proof by providing:
- Basic clause processing utilities
- Properties of satisfied clauses under variable assignment
- Core filtering and counting theorems
-/

-- Basic helper: When a clause is satisfied, processClauseForVariableAssignment returns none
theorem processClause_satisfied_returns_none {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (value : Bool)
    (h_satisfied : Clause.satisfiedBy clause var value = true) :
    processClauseForVariableAssignment clause var value = none := by
  unfold processClauseForVariableAssignment
  rw [if_pos h_satisfied]

-- Basic helper: When a clause is not satisfied, processClauseForVariableAssignment returns a clause without the variable
theorem processClause_unsatisfied_removes_variable {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (value : Bool)
    (_h_contains : Clause.containsVariable clause var = true)
    (h_not_satisfied : Clause.satisfiedBy clause var value = false) :
    ∃ result_clause, processClauseForVariableAssignment clause var value = some result_clause ∧
    Clause.containsVariable result_clause var = false := by
  unfold processClauseForVariableAssignment
  rw [if_neg (by
    intro h_true
    rw [h_true] at h_not_satisfied
    cases h_not_satisfied
  )]

  -- The filtered clause is our witness
  let filtered_clause := clause.filter fun lit => ¬(lit.containsVariable var)

  -- Provide the existential witness
  apply Exists.intro filtered_clause

  constructor
  · rfl
  · unfold Clause.containsVariable
    rw [List.any_eq_false]
    intro lit h_lit_in_filtered
    rw [List.mem_filter] at h_lit_in_filtered
    obtain ⟨h_lit_in_orig, h_not_contains_var⟩ := h_lit_in_filtered
    have h_decide : decide (¬lit.containsVariable var = true) = true := h_not_contains_var
    rw [decide_eq_true_iff] at h_decide
    exact h_decide

-- Helper: Combined theorem - processClauseForVariableAssignment removes the variable from the clause
theorem processClause_removes_variable {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (value : Bool)
    (h_contains : Clause.containsVariable clause var = true) :
    processClauseForVariableAssignment clause var value = none ∨
    (∃ result_clause, processClauseForVariableAssignment clause var value = some result_clause ∧
     Clause.containsVariable result_clause var = false) := by
  by_cases h_satisfied : Clause.satisfiedBy clause var value = true
  · left
    exact processClause_satisfied_returns_none clause var value h_satisfied
  · right
    have h_not_satisfied : Clause.satisfiedBy clause var value = false := by
      by_cases h : Clause.satisfiedBy clause var value = false
      · exact h
      · exfalso
        have h_bool : Clause.satisfiedBy clause var value = true ∨ Clause.satisfiedBy clause var value = false := by
          cases Clause.satisfiedBy clause var value <;> simp
        cases h_bool with
        | inl h_true => exact h_satisfied h_true
        | inr h_false => exact h h_false
    exact processClause_unsatisfied_removes_variable clause var value h_contains h_not_satisfied

-- Helper: Core theorem about filtering removing elements
theorem filter_removes_element_strict {α : Type} (l : List α) (p : α → Bool) (x : α)
    (h_mem : x ∈ l) (h_not_mem : x ∉ l.filter p) :
    (l.filter p).length < l.length := by
  have h_split : l.length = (l.filter p).length + (l.filter (fun a => ¬p a)).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.length_eq_countP_add_countP p

  have h_p_false : p x = false := by
    by_contra h_contra
    cases h : p x with
    | false => contradiction
    | true =>
      have h_in : x ∈ l.filter p := by
        rw [List.mem_filter]
        exact ⟨h_mem, h⟩
      exact h_not_mem h_in

  have h_in_complement : x ∈ l.filter (fun a => ¬p a) := by
    rw [List.mem_filter]
    constructor
    · exact h_mem
    · simp [h_p_false]

  have h_pos : 0 < (l.filter (fun a => ¬p a)).length := by
    by_contra h_not_pos
    push_neg at h_not_pos
    have h_zero : (l.filter (fun a => ¬p a)).length = 0 := Nat.eq_zero_of_le_zero h_not_pos
    have h_empty : l.filter (fun a => ¬p a) = [] := List.length_eq_zero_iff.mp h_zero
    rw [h_empty] at h_in_complement
    exact List.not_mem_nil h_in_complement

  rw [h_split]
  exact Nat.lt_add_of_pos_right h_pos

-- Helper: When a literal contains a variable, it gets filtered out
theorem literal_with_var_filtered_out {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (lit : Literal Var)
    (_h_lit_mem : List.Mem lit clause) (h_lit_has_var : lit.containsVariable var = true) :
    ¬List.Mem lit (clause.filter (fun l => ¬(l.containsVariable var))) := by
  intro h_in_filtered
  have h_mem_filter := List.mem_filter.mp h_in_filtered
  obtain ⟨h_in_orig, h_not_contains⟩ := h_mem_filter
  have h_decide_contra : decide (¬lit.containsVariable var = true) = true := h_not_contains
  rw [decide_eq_true_iff] at h_decide_contra
  rw [h_lit_has_var] at h_decide_contra
  simp at h_decide_contra

/--
Helper theorem: If a clause survives processing when the original contained the variable,
then the result doesn't contain the variable.

This handles the case where `processClause_removes_variable` returns `some`.
-/
private theorem processed_clause_no_variable_when_original_contained {Var : Type} [DecidableEq Var]
    (orig_clause : Clause Var) (clause : Clause Var) (var : Var) (value : Bool)
    (h_orig_contains : Clause.containsVariable orig_clause var = true)
    (h_process_result : processClauseForVariableAssignment orig_clause var value = some clause) :
    Clause.containsVariable clause var = false := by
  have h_or := processClause_removes_variable orig_clause var value h_orig_contains
  cases h_or with
  | inl h_none =>
    -- Contradiction: processClause returned some but should return none
    rw [h_none] at h_process_result
    cases h_process_result
  | inr h_some =>
    -- Extract the result clause and its property
    obtain ⟨result_clause, h_eq, h_no_var⟩ := h_some
    rw [h_eq] at h_process_result
    have h_clause_eq : result_clause = clause := by
      cases h_process_result
      rfl
    rw [← h_clause_eq]
    exact h_no_var

/--
Helper theorem: Filtered clauses don't contain the filtered variable.

When a clause is processed by filtering out literals containing a variable,
the result cannot contain that variable.
-/
private theorem filtered_clause_no_variable {Var : Type} [DecidableEq Var]
    (orig_clause : Clause Var) (var : Var) :
    Clause.containsVariable (orig_clause.filter (fun lit => ¬(lit.containsVariable var))) var = false := by
  unfold Clause.containsVariable
  rw [List.any_eq_false]
  intro lit h_lit_in_filtered
  rw [List.mem_filter] at h_lit_in_filtered
  obtain ⟨_, h_not_contains_lit⟩ := h_lit_in_filtered
  have h_decide : decide (¬lit.containsVariable var = true) = true := h_not_contains_lit
  rw [decide_eq_true_iff] at h_decide
  exact h_decide

/--
Helper theorem: If original clause doesn't contain the variable, process it accordingly.

When the original clause doesn't contain the variable, either it gets satisfied and removed,
or it gets filtered (but filtering doesn't change it since no literals contain the variable).
-/
private theorem process_clause_when_no_variable {Var : Type} [DecidableEq Var]
    (orig_clause : Clause Var) (clause : Clause Var) (var : Var) (value : Bool)
    (h_process_result : processClauseForVariableAssignment orig_clause var value = some clause) :
    Clause.containsVariable clause var = false := by
  unfold processClauseForVariableAssignment at h_process_result
  by_cases h_satisfied : Clause.satisfiedBy orig_clause var value = true
  · -- Original clause is satisfied, so it should be removed (contradiction)
    rw [if_pos h_satisfied] at h_process_result
    cases h_process_result
  · -- Original clause is not satisfied, so it gets filtered
    rw [if_neg h_satisfied] at h_process_result
    have h_clause_eq : clause = orig_clause.filter (fun lit => ¬(lit.containsVariable var)) := by
      cases h_process_result
      rfl
    rw [h_clause_eq]
    exact filtered_clause_no_variable orig_clause var

/--
**Main Property**: After setting a variable, no clause in the result contains that variable.

This is a key invariant of variable assignment: once a variable is set, it's completely
eliminated from the formula. Clauses are either:
1. **Satisfied and removed** (if they contained a literal that became true)
2. **Filtered** (literals containing the variable are removed)

In both cases, the variable no longer appears in any remaining clause.

## Proof Strategy

1. Extract the original clause that produced the result clause
2. **Case 1**: Original contained the variable → use `processClause_removes_variable`
3. **Case 2**: Original didn't contain the variable → filtering preserves this property
-/
theorem setVariable_removes_variable {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool) (clause : Clause Var)
    (h_clause_in_result : List.Mem clause (formula.setVariable var value)) :
    Clause.containsVariable clause var = false := by
  -- Extract the original clause that produced this result clause
  unfold Formula.setVariable at h_clause_in_result
  have h_exists : ∃ orig_clause, List.Mem orig_clause formula ∧ processClauseForVariableAssignment orig_clause var value = some clause := by
    exact List.mem_filterMap.mp h_clause_in_result
  obtain ⟨orig_clause, h_orig_mem, h_process_result⟩ := h_exists

  -- Case analysis: did the original clause contain the variable?
  by_cases h_contains : Clause.containsVariable orig_clause var = true
  · -- Case 1: Original contained the variable
    exact processed_clause_no_variable_when_original_contained orig_clause clause var value h_contains h_process_result
  · -- Case 2: Original didn't contain the variable
    have h_not_contains : Clause.containsVariable orig_clause var = false := by
      by_contra h_contra
      push_neg at h_contra
      cases h_bool : Clause.containsVariable orig_clause var with
      | true => exact h_contains h_bool
      | false => exact h_contra h_bool
    exact process_clause_when_no_variable orig_clause clause var value h_process_result
