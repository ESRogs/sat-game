import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.Util.List
import SATGame.FormulaOps.Termination.Nonterminal

/-!
# Remove Clause Termination

Proves that removing clauses decreases literal count.

Key: Nonterminal formulas have no empty clauses, so removing any clause
removes at least one literal.
-/

theorem removeClause_decreases_literalCount {Var : Type} (formula : Formula Var) (index : Nat)
    (h_nonterminal : formula.isNonterminal = true)
    (h_index : index < formula.length) :
    (formula.removeClause index).countLiterals < formula.countLiterals := by
  -- The key insight: nonterminal formulas have no empty clauses,
  -- so the clause we're removing must contain at least one literal
  have h_clause_nonempty := clause_at_index_nonempty formula index h_nonterminal h_index
  -- Apply the general list utility: removing an element with positive
  -- contribution (clause.length > 0) decreases the total sum (literalCount)
  apply sum_eraseIdx_lt formula (fun clause => clause.length) index h_index h_clause_nonempty

/--
**Clause Removal Sequences are Nonincreasing**: Any sequence of clause removals
can only decrease or maintain the literal count.

This fundamental property shows that clause removal operations are "safe" in the sense
that they never increase the complexity (literal count) of a formula.
-/
theorem clause_removal_sequence_nonincreasing {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (removals : List (FormulaOp Var))
    (h_all_removals : ∀ op ∈ removals, ∃ index, op = FormulaOp.RemoveClause index) :
    (removals.foldl Formula.applyOp formula).countLiterals ≤ formula.countLiterals := by
  -- Induction on the list of removal operations
  induction removals generalizing formula with
  | nil =>
    -- Base case: empty list of operations
    simp [List.foldl_nil]
  | cons op rest ih =>
    -- Inductive case: op :: rest
    simp [List.foldl_cons]
    -- Show that op is a removeClause operation
    obtain ⟨index, h_op_eq⟩ := h_all_removals op (by simp)
    -- Show that removeClause is nonincreasing
    have h_single_nonincreasing : (formula.applyOp op).countLiterals ≤ formula.countLiterals := by
      rw [h_op_eq]
      unfold Formula.applyOp Formula.removeClause Formula.countLiterals
      -- removeClause always decreases or preserves literal count
      by_cases h_index : index < formula.length
      · -- Valid index: erasing an element never increases the sum
        have h_eraseIdx_le : ((formula.eraseIdx index).map List.length).sum ≤ (formula.map List.length).sum := by
          -- This is a general property: removing an element from a list never increases the sum
          exact List.sum_map_eraseIdx_le formula List.length index
        exact h_eraseIdx_le
      · -- Invalid index: no change (eraseIdx does nothing)
        simp [List.eraseIdx_of_length_le (Nat.le_of_not_gt h_index)]
    -- Apply the inductive hypothesis to the rest of the operations on the new formula
    have ih_applied := ih (formula.applyOp op) (by
      intros op' h_mem
      exact h_all_removals op' (List.mem_cons_of_mem op h_mem))
    -- Combine: first operation is nonincreasing, then rest is nonincreasing
    -- ih_applied shows: (rest.foldl Formula.applyOp (formula.applyOp op)).countLiterals ≤ (formula.applyOp op).countLiterals
    -- h_single_nonincreasing shows: (formula.applyOp op).countLiterals ≤ formula.countLiterals
    exact Nat.le_trans ih_applied h_single_nonincreasing
