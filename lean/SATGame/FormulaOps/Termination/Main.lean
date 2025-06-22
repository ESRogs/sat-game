import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.Termination.RemoveClause
import SATGame.FormulaOps.Termination.SetVariable

/-!
# Main Termination Theorem

Establishes the central result: **formula operations always terminate**.

## Approach

Termination is proven using literal count as a well-founded measure:
- Every valid operation on nonterminal formulas decreases literal count
- Natural number ordering ensures no infinite descending chains
- Component proofs handle `setVariable` and `removeClause` separately
-/

/--
Relation defining when one formula has strictly fewer literals than another.

This serves as our termination measure: every valid operation on a nonterminal
formula produces a formula with a lower literal count, and natural number ordering
is well-founded.
-/
def HasLowerLiteralCount {Var : Type} : Formula Var → Formula Var → Prop :=
  InvImage (· < ·) Formula.countLiterals

/--
**Main Termination Theorem**: The literal count relation is well-founded.

This fundamental result establishes that there are no infinite descending chains
of formulas under our termination ordering. Combined with the fact that every
operation decreases literal count, this proves formula operations always terminate.
-/
theorem operations_eventually_terminate {Var : Type} :
    WellFounded (HasLowerLiteralCount : Formula Var → Formula Var → Prop) := by
  apply InvImage.wf
  exact Nat.lt_wfRel.wf

/--
**Master Termination Result**: Every valid operation decreases literal count.

This theorem unifies all termination proofs, showing that regardless of which
operation is applied (variable assignment or clause removal), the literal count
strictly decreases for any nonterminal formula.
-/
theorem operation_decreases_literalCount {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (op : FormulaOp Var)
    (h_nonterminal : formula.isNonterminal = true)
    (h_applicable : op.IsApplicable formula) :
    (formula.applyOp op).countLiterals < formula.countLiterals := by
  cases op with
  | SetVariable var value =>
    -- Apply setVariable termination theorem
    apply setVariable_decreases_literalCount formula var value h_nonterminal
    -- The goal is: (List.any formula fun clause => Clause.containsVariable clause var) = true
    -- We have h_applicable : (FormulaOp.SetVariable var value).IsApplicable formula
    -- which unfolds to: formula.containsVariable var = true
    -- These are exactly the same after unfolding definitions
    unfold FormulaOp.IsApplicable at h_applicable
    exact h_applicable
  | RemoveClause index =>
    -- Apply removeClause termination theorem
    apply removeClause_decreases_literalCount formula index h_nonterminal
    -- Need to prove index is valid (follows from IsApplicable)
    unfold FormulaOp.IsApplicable at h_applicable
    simp at h_applicable
    exact h_applicable
