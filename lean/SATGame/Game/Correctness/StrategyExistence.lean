import SATGame.CNF.Satisfiability
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.SatisfiabilityPreservation
import SATGame.FormulaOps.Termination.Nonterminal

/-!
# Strategy Existence Properties 🚧 IN PROGRESS

This module contains the strategy existence properties for the SAT Game.
These ensure that players with winning positions can maintain their advantage through correct play.

The theorems here provide strategic interpretations of the mathematical preservation
properties proven in FormulaOps/SatisfiabilityPreservation.lean.

1. `satisfiable_has_preserving_setVariable`: Satisfiable nonterminal formulas have preserving variable assignments
2. `unsatisfiable_nonminimal_has_preserving_removeClause`: Unsatisfiable non-minimal formulas have preserving clause removals
-/

/--
**Strategy Existence for Affirmative**: If a formula is satisfiable and nonterminal,
there exists a variable assignment that keeps it satisfiable.

This is the key result showing that Affirmative (trying to satisfy) can always make progress
when they have a winning position (satisfiable formula).

This theorem provides the strategic interpretation of the mathematical theorem
`satisfiable_nonterminal_has_preserving_assignment`.
-/
theorem satisfiable_has_preserving_setVariable {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_satisfiable : formula.IsSatisfiable)
    (h_nonterminal : formula.isNonterminal = true) :
    ∃ (var : Var) (value : Bool),
      formula.containsVariable var = true ∧
      (formula.setVariable var value).IsSatisfiable :=
  -- This is exactly the mathematical theorem with strategic interpretation
  satisfiable_nonterminal_has_preserving_assignment formula h_satisfiable h_nonterminal

/--
**Strategy Existence for Negative**: If a formula is unsatisfiable but not a minimal core,
there exists a clause removal that keeps it unsatisfiable.

This is the key result showing that Negative (trying to falsify) can always make progress
when they have a winning position (unsatisfiable formula) that isn't already minimal.
-/
theorem unsatisfiable_nonminimal_has_preserving_removeClause {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_unsatisfiable : ¬formula.IsSatisfiable)
    (h_nonminimal : ¬formula.IsMinimalUnsatisfiableCore) :
    ∃ (index : Nat),
      index < formula.length ∧
      ¬(formula.removeClause index).IsSatisfiable := by
  -- Since the formula is not a minimal unsatisfiable core, there exists some clause
  -- that is redundant - removing it preserves unsatisfiability.
  -- This follows from the definition of minimal unsatisfiable core.
  unfold Formula.IsMinimalUnsatisfiableCore at h_nonminimal
  simp only [not_and] at h_nonminimal
  -- h_nonminimal : ¬formula.IsSatisfiable → ¬∀ (index : Nat), index < List.length formula → (formula.removeClause index).IsSatisfiable
  have h_not_forall := h_nonminimal h_unsatisfiable
  -- h_not_forall : ¬∀ (index : Nat), index < List.length formula → (formula.removeClause index).IsSatisfiable

  -- Convert the negated universal to an existential
  rw [Classical.not_forall] at h_not_forall
  -- h_not_forall : ∃ index, ¬(index < List.length formula → (formula.removeClause index).IsSatisfiable)
  obtain ⟨index, h_index_property⟩ := h_not_forall

  -- Simplify the implication negation
  rw [Classical.not_imp] at h_index_property
  -- h_index_property : index < List.length formula ∧ ¬(formula.removeClause index).IsSatisfiable
  obtain ⟨h_bound, h_unsat⟩ := h_index_property
  exact ⟨index, h_bound, by
    -- formula.removeClause is defined as List.eraseIdx
    unfold Formula.removeClause
    exact h_unsat⟩
