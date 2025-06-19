import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.ByContra
import SATGame.CNF.Formula
import SATGame.FormulaOps.FormulaExt

/-!
# Nonterminal Formulas

Defines formulas that are neither empty nor contain empty clauses.

This module contains:
- Core insights about nonterminal formulas
- Properties connecting nonterminal status to empty clauses
- Helper theorems about clause lengths in nonterminal formulas
- Basic structural properties (non-emptiness, variable containment)
-/

-- A. Core insight: Nonterminal formulas have no empty clauses
theorem nonterminal_implies_no_empty_clauses {Var : Type} (formula : Formula Var)
    (h : formula.isNonterminal = true) : Formula.hasEmptyClause formula = false := by
  -- Use the definition of isNonterminal
  unfold Formula.isNonterminal at h
  unfold Formula.isTerminal at h
  -- h : (formula.isEmpty || formula.hasEmptyClause) = false = true
  -- This means: formula.isEmpty || formula.hasEmptyClause = false
  -- Since OR is false, both parts must be false
  simp at h
  -- h is now: ¬formula.isEmpty ∧ ¬formula.hasEmptyClause
  exact h.2

-- B. Helper: Any clause at valid index in nonterminal formula is nonempty
theorem clause_at_index_nonempty {Var : Type} (formula : Formula Var) (index : Nat)
    (h_nonterminal : formula.isNonterminal = true)
    (h_index : index < formula.length) :
    (formula.get ⟨index, h_index⟩).length > 0 := by
  -- We know nonterminal formulas have no empty clauses
  have h_no_empty := nonterminal_implies_no_empty_clauses formula h_nonterminal

  -- By contradiction: assume the clause is empty
  by_contra h_not_pos
  -- h_not_pos : ¬(formula.get ⟨index, h_index⟩).length > 0
  -- This means the length is 0
  have h_zero_length : (formula.get ⟨index, h_index⟩).length = 0 := by
    -- In Nat, ¬(n > 0) means n = 0
    exact Nat.eq_zero_of_not_pos h_not_pos

  -- If the clause has length 0, it's empty
  have h_clause_empty : (formula.get ⟨index, h_index⟩).isEmpty := by
    unfold Clause.isEmpty
    rw [List.isEmpty_iff_length_eq_zero]
    exact h_zero_length

  -- But then formula.hasEmptyClause = true (since this clause is in the formula)
  have h_has_empty : Formula.hasEmptyClause formula = true := by
    unfold Formula.hasEmptyClause
    rw [List.any_eq_true]
    exact ⟨formula.get ⟨index, h_index⟩, List.get_mem formula ⟨index, h_index⟩, h_clause_empty⟩

  -- This contradicts h_no_empty
  rw [h_has_empty] at h_no_empty
  simp at h_no_empty

-- C. Basic structural property: Nonterminal formulas are not empty
theorem nonterminal_nonempty {Var : Type} (formula : Formula Var)
    (h_nonterminal : formula.isNonterminal = true) :
    formula ≠ [] := by
  unfold Formula.isNonterminal Formula.isTerminal at h_nonterminal
  simp at h_nonterminal
  exact h_nonterminal.1

/--
**Nonterminal Variable Containment**: Every nonterminal formula contains at least one variable.

This is a fundamental property showing that nonterminal formulas are non-trivial:
they must contain variables that can be assigned during formula operations.

The proof decomposes the structural hierarchy formula → clause → literal → variable
through 8 logical steps, ensuring each level is non-empty and extracting components
until a variable is found.
-/
theorem nonterminal_contains_variable {Var : Type} [DecidableEq Var] (formula : Formula Var)
    (h_nonterminal : formula.isNonterminal = true) :
    ∃ var, formula.containsVariable var = true := by
  -- Step 1: Formula is not empty
  have h_formula_nonempty : formula ≠ [] := nonterminal_nonempty formula h_nonterminal

  -- Step 2: Extract a clause from non-empty formula
  have h_formula_length : formula.length > 0 := by
    cases formula with
    | nil => contradiction
    | cons _ _ => simp

  -- Get the first clause (at index 0)
  have h_clause_exists : ∃ (clause : Clause Var), List.Mem clause formula := by
    use formula.get ⟨0, h_formula_length⟩
    exact List.get_mem formula ⟨0, h_formula_length⟩

  -- Extract the clause and its membership proof
  obtain ⟨clause, h_clause_in⟩ := h_clause_exists

  -- Step 3: Show the clause is not empty
  have h_clause_nonempty : clause ≠ [] := by
    -- We need to show this clause has no empty clauses
    have h_no_empty_clauses := nonterminal_implies_no_empty_clauses formula h_nonterminal
    -- If clause were empty, then formula would have an empty clause
    by_contra h_clause_empty
    have h_clause_isEmpty : clause.isEmpty = true := by
      unfold Clause.isEmpty
      rw [List.isEmpty_iff_length_eq_zero]
      simp [h_clause_empty]
    -- This would mean formula.hasEmptyClause = true
    have h_has_empty : formula.hasEmptyClause = true := by
      unfold Formula.hasEmptyClause
      rw [List.any_eq_true]
      exact ⟨clause, h_clause_in, h_clause_isEmpty⟩
    -- But we know hasEmptyClause = false
    rw [h_has_empty] at h_no_empty_clauses
    simp at h_no_empty_clauses

  -- Step 4: Extract a literal from non-empty clause
  have h_clause_length : clause.length > 0 := by
    cases clause with
    | nil => contradiction
    | cons _ _ => simp

  have h_literal_exists : ∃ (literal : Literal Var), List.Mem literal clause := by
    use clause.get ⟨0, h_clause_length⟩
    exact List.get_mem clause ⟨0, h_clause_length⟩

  obtain ⟨literal, h_literal_in⟩ := h_literal_exists

  -- Step 5: Extract variable from literal
  have h_literal_has_var : ∃ var, literal.containsVariable var = true := literal_contains_variable literal
  obtain ⟨var, h_var_in_literal⟩ := h_literal_has_var

  -- Step 6: Show clause contains the variable
  have h_clause_contains_var : clause.containsVariable var = true :=
    literal_var_implies_clause_var clause var ⟨literal, h_literal_in, h_var_in_literal⟩

  -- Step 7: Show formula contains the variable
  have h_formula_contains_var : formula.containsVariable var = true :=
    clause_var_implies_formula_var formula var ⟨clause, h_clause_in, h_clause_contains_var⟩

  -- Step 8: Conclude existence
  exact ⟨var, h_formula_contains_var⟩
