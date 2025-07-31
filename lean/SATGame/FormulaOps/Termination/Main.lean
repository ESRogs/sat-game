import Mathlib.Data.List.TakeDrop
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.FormulaOps.Termination.RemoveClause
import SATGame.FormulaOps.Termination.SetVariable
import SATGame.Util.List

/-!
# Main Termination Theorem

Establishes the central result: **formula operations always terminate**.

## Theorem Hierarchy

1. **operation_decreases_literalCount**: Each valid operation on a nonterminal formula
   strictly decreases the literal count
2. **HasLowerLiteralCount_wellFounded**: The literal count ordering is well-founded
   (no infinite descending chains)
3. **operations_bounded_by_literalCount**: Any sequence of valid operations is bounded
   by the initial literal count

Together, these theorems prove that sequences of formula operations must terminate.
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
The literal count relation is well-founded.

This establishes that there are no infinite descending chains of formulas under
the literal count ordering. This technical property is used to prove that
sequences of operations must terminate.
-/
theorem HasLowerLiteralCount_wellFounded {Var : Type} :
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

/-- Apply a list of operations sequentially to a formula -/
def Formula.applyOps {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var)) : Formula Var :=
  ops.foldl Formula.applyOp formula

/-- Sequential application of operations: applying op::rest equals applying op then rest -/
lemma Formula.applyOps_cons {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (op : FormulaOp Var) (rest : List (FormulaOp Var)) :
    formula.applyOps (op :: rest) = (formula.applyOp op).applyOps rest := by
  simp [Formula.applyOps, List.foldl_cons]

/-- Taking first n+1 operations from op::rest and applying them is equivalent to
    applying op then taking first n operations from rest -/
lemma applyOps_take_cons_succ {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (op : FormulaOp Var) (rest : List (FormulaOp Var)) (n : Nat) :
    formula.applyOps ((op :: rest).take (n + 1)) = (formula.applyOp op).applyOps (rest.take n) := by
  -- Direct simplification using list properties
  simp [Formula.applyOps, List.foldl_cons, List.take_cons]

/-- Applying operations from two lists sequentially is equivalent to applying the concatenated list -/
lemma Formula.applyOps_append {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops1 ops2 : List (FormulaOp Var)) :
    formula.applyOps (ops1 ++ ops2) = (formula.applyOps ops1).applyOps ops2 := by
  unfold Formula.applyOps
  rw [List.foldl_append]

/-- Empty formulas remain empty under any sequence of operations -/
lemma empty_formula_applyOps {Var : Type} [DecidableEq Var] (ops : List (FormulaOp Var)) :
    Formula.applyOps ([] : Formula Var) ops = [] := by
  induction ops with
  | nil =>
    -- Base case: no operations applied to empty formula
    simp [Formula.applyOps]
  | cons op rest ih =>
    -- Inductive case: apply operation then rest of operations
    rw [Formula.applyOps_cons]
    -- Goal: (Formula.applyOp ([] : Formula Var) op).applyOps rest = []
    -- First show Formula.applyOp ([] : Formula Var) op = []
    have h_op_empty : Formula.applyOp ([] : Formula Var) op = [] := by
      cases op with
      | SetVariable var value =>
        -- Empty formula setVariable returns empty
        simp [Formula.applyOp, Formula.setVariable, List.filterMap_nil]
      | RemoveClause index =>
        -- Empty formula removeClause returns empty
        simp [Formula.applyOp, Formula.removeClause, List.eraseIdx_nil]
    -- Now apply inductive hypothesis
    rw [h_op_empty]
    exact ih

/-- Empty clauses cannot be satisfied by any variable assignment -/
lemma empty_clause_not_satisfied {Var : Type} [DecidableEq Var] (var : Var) (value : Bool) :
  ¬Clause.satisfiedBy ([] : Clause Var) var value := by
  unfold Clause.satisfiedBy
  simp [List.any_nil]

/-- Processing an empty clause for variable assignment always returns an empty clause -/
lemma processClause_preserves_empty {Var : Type} [DecidableEq Var] (var : Var) (value : Bool) :
  processClauseForVariableAssignment ([] : Clause Var) var value = some [] := by
  unfold processClauseForVariableAssignment
  -- Use our lemma that empty clauses are never satisfied
  have h_not_satisfied := empty_clause_not_satisfied var value
  simp [h_not_satisfied, List.filter_nil]

/-- setVariable preserves the existence of empty clauses -/
lemma setVariable_preserves_hasEmptyClause {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool) :
    formula.hasEmptyClause = true → (formula.setVariable var value).hasEmptyClause = true := by
  intro h_has_empty
  unfold Formula.hasEmptyClause at h_has_empty ⊢
  unfold Formula.setVariable
  -- We have an empty clause in the original formula
  rw [List.any_eq_true] at h_has_empty
  obtain ⟨empty_clause, h_in_formula, h_isEmpty⟩ := h_has_empty
  -- Show that the result of setVariable also has an empty clause
  rw [List.any_eq_true]
  -- Since the empty clause gets mapped to some [], it appears in the filterMap result
  have h_process_result := processClause_preserves_empty var value
  have h_empty_eq : empty_clause = [] := by
    unfold Clause.isEmpty at h_isEmpty
    rw [List.isEmpty_iff] at h_isEmpty
    exact h_isEmpty
  -- The empty clause maps to some [] and appears in the result
  use []
  constructor
  · -- Show [] is in the filterMap result
    rw [List.mem_filterMap]
    use empty_clause
    constructor
    · exact h_in_formula
    · rw [h_empty_eq]
      exact h_process_result
  · -- Show [] is empty
    simp [Clause.isEmpty]


-- Strategy-Based Termination: Any valid strategy reaches terminal within literal count bound

/--
Result of applying a strategy to a formula.
Either the formula is terminal (game over) or we get an operation to continue.
This avoids dependent types in the recursion by making the strategy handle the branching.
-/
inductive StrategyResult (Var : Type) [DecidableEq Var] (f : Formula Var) where
  | Terminal : f.isTerminal = true → StrategyResult Var f
  | Continue : (op : FormulaOp Var) → op.IsApplicable f → StrategyResult Var f

/--
A strategy is a function that returns a result for any formula.
The result either proves the formula is terminal or provides a valid operation.
This captures the game-theoretic notion of "how to play" while avoiding dependent type issues.
-/
def Strategy (Var : Type) [DecidableEq Var] :=
  (f : Formula Var) → StrategyResult Var f

/--
A strategy is well-formed if it respects the terminal/nonterminal distinction:
- Returns Terminal when formula is terminal
- Returns Continue when formula is nonterminal
-/
def WellFormedStrategy {Var : Type} [DecidableEq Var] (strategy : Strategy Var) : Prop :=
  ∀ f : Formula Var,
    (f.isTerminal = true → ∃ h, strategy f = .Terminal h) ∧
    (f.isNonterminal = true → ∃ op h, strategy f = .Continue op h)

/--
Apply a strategy iteratively for n steps, stopping early if the formula becomes terminal.
This models playing a game according to a strategy until either terminal state or step limit.
With the new StrategyResult type, there's no dependent if-then-else!
-/
def iterateStrategy {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (strategy : Strategy Var) : Nat → Formula Var
  | 0 => formula
  | n+1 =>
    let f := iterateStrategy formula strategy n
    match strategy f with
    | .Terminal _ => f
    | .Continue op _ => f.applyOp op
-- TODO: Prove that nonterminal formulas always have applicable operations
-- theorem nonterminal_has_applicable_operation {Var : Type} [DecidableEq Var]
--     (formula : Formula Var) (h_nt : formula.isNonterminal = true) :
--     ∃ op : FormulaOp Var, op.IsApplicable formula

-- With the new StrategyResult approach, the shift property becomes much simpler!

-- Key observation: One step of iteration equals the strategy result
lemma iterateStrategy_one_step {Var : Type} [DecidableEq Var]
    (f : Formula Var) (strategy : Strategy Var) :
    iterateStrategy f strategy 1 =
      match strategy f with
      | .Terminal _ => f
      | .Continue op _ => f.applyOp op := by
  simp [iterateStrategy]

-- Key recursive equality: shifting iteration by one step
lemma iterateStrategy_shift_equality {Var : Type} [DecidableEq Var]
    (f : Formula Var) (strategy : Strategy Var) (op : FormulaOp Var)
    (h_op_applicable : op.IsApplicable f) (n : Nat)
    (h_strat : strategy f = .Continue op h_op_applicable) :
    iterateStrategy f strategy (n + 1) = iterateStrategy (f.applyOp op) strategy n := by
  -- Key insight: both sides follow the same recursive pattern after the first step
  induction n with
  | zero =>
    -- Base case: n = 0
    -- LHS: iterateStrategy f strategy 1 = (match strategy f with | Terminal => f | Continue op => f.applyOp op)
    -- RHS: iterateStrategy (f.applyOp op) strategy 0 = f.applyOp op
    -- Since strategy f = Continue op, LHS = f.applyOp op = RHS
    rw [iterateStrategy_one_step]
    rw [h_strat]
    simp [iterateStrategy]
  | succ k ih =>
    -- Inductive case: n = k + 1
    -- Use the recursive definition of iterateStrategy directly
    -- LHS: iterateStrategy f strategy (k + 2)
    -- RHS: iterateStrategy (f.applyOp op) strategy (k + 1)

    -- Unfold LHS: iterateStrategy f strategy (k + 2) = apply strategy to (iterateStrategy f strategy (k + 1))
    -- By IH: iterateStrategy f strategy (k + 1) = iterateStrategy (f.applyOp op) strategy k
    -- So LHS = apply strategy to (iterateStrategy (f.applyOp op) strategy k)

    -- Unfold RHS: iterateStrategy (f.applyOp op) strategy (k + 1) = apply strategy to (iterateStrategy (f.applyOp op) strategy k)

    -- Therefore LHS = RHS
    unfold iterateStrategy
    -- After unfolding, both sides should be identical
    rw [ih]

-- Note: We're removing the complex shift lemma and using bounded iteration instead
-- This eliminates the dependent type issues we were struggling with

/--
**Core Iteration Shift Lemma**: The mathematical heart of the termination proof.

If a formula f takes one step to become g via a strategy, and g terminates within n steps,
then f terminates within n+1 steps. This connects the well-founded induction hypothesis
to the main goal without dependent type complications.
-/
lemma iterateStrategy_shift_step {Var : Type} [DecidableEq Var]
    (f : Formula Var) (strategy : Strategy Var) (op : FormulaOp Var)
    (h_op_applicable : op.IsApplicable f) (n : Nat)
    (h_strat : strategy f = .Continue op h_op_applicable)
    (h_terminal : (iterateStrategy (f.applyOp op) strategy n).isTerminal = true) :
    (iterateStrategy f strategy (n + 1)).isTerminal = true := by
  -- Key insight: We need to show that iterating from f for n+1 steps is terminal
  -- We know that iterating from (f.applyOp op) for n steps is terminal
  -- The connection is through the recursive structure of iterateStrategy

  -- First, let's understand what happens step by step:
  -- iterateStrategy f strategy (n + 1) applies the strategy to the result of n steps
  -- But the result after n steps from f should be the same as after n-1 steps from f.applyOp op

  -- Use induction on n to establish the recursive connection
  induction n with
  | zero =>
    -- Base case: n = 0
    -- Goal: (iterateStrategy f strategy 1).isTerminal = true
    -- Given: (iterateStrategy (f.applyOp op) strategy 0).isTerminal = true
    -- Since iterateStrategy ... 0 = identity, we have: (f.applyOp op).isTerminal = true

    -- Simplify the hypothesis: iterateStrategy (f.applyOp op) strategy 0 = f.applyOp op
    have h_identity : iterateStrategy (f.applyOp op) strategy 0 = f.applyOp op := by
      simp [iterateStrategy]
    rw [h_identity] at h_terminal
    -- Now h_terminal : (f.applyOp op).isTerminal = true

    -- Show the goal using the one-step lemma
    rw [iterateStrategy_one_step]
    rw [h_strat]
    -- Goal becomes: (f.applyOp op).isTerminal = true
    exact h_terminal

  | succ k ih =>
    -- Inductive case: n = k + 1
    -- Goal: (iterateStrategy f strategy (k + 2)).isTerminal = true
    -- Given: (iterateStrategy (f.applyOp op) strategy (k + 1)).isTerminal = true

    -- Use our shift equality lemma!
    -- We know: iterateStrategy f strategy (k + 2) = iterateStrategy (f.applyOp op) strategy (k + 1)
    rw [iterateStrategy_shift_equality f strategy op h_op_applicable (k + 1) h_strat]
    -- Now the goal becomes: (iterateStrategy (f.applyOp op) strategy (k + 1)).isTerminal = true
    -- This is exactly our hypothesis!
    exact h_terminal

/--
Monotonicity of iteration: if a formula terminates in m steps, it also terminates in k steps for any k ≥ m.
This is because once a formula becomes terminal, it stays terminal under further iterations.
-/
-- Simple monotonicity lemma - if formula terminates in m steps, it terminates in more steps
lemma iterateStrategy_monotonic {Var : Type} [DecidableEq Var]
    (f : Formula Var) (strategy : Strategy Var) (m k : Nat)
    (h_wf : WellFormedStrategy strategy)
    (h_le : m ≤ k)
    (h_term : (iterateStrategy f strategy m).isTerminal = true) :
    (iterateStrategy f strategy k).isTerminal = true := by
  -- Express k = m + d and induct on d
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h_le

  -- Induction on d
  induction d with
  | zero =>
    -- Base case: k = m + 0 = m
    simp
    exact h_term

  | succ d ih =>
    -- Inductive step: k = m + (d + 1) = (m + d) + 1
    -- IH: (iterateStrategy f strategy (m + d)).isTerminal = true
    -- Goal: (iterateStrategy f strategy (m + d + 1)).isTerminal = true

    -- Let g = iterateStrategy f strategy (m + d)
    let g := iterateStrategy f strategy (m + d)
    have h_g_terminal : g.isTerminal = true := by
      apply ih
      simp [Nat.le_add_right]

    -- Goal: (iterateStrategy f strategy (m + d + 1)).isTerminal = true
    -- By definition: this is (iterateStrategy f strategy ((m + d) + 1))
    simp [Nat.add_assoc] at *
    simp [iterateStrategy]

    -- Since g is terminal and strategy is well-formed, strategy g returns Terminal
    have h_strat_terminal : ∃ h, strategy g = .Terminal h := by
      exact (h_wf g).1 h_g_terminal

    -- Extract the witness and apply
    obtain ⟨h_proof, h_eq_strat⟩ := h_strat_terminal
    rw [h_eq_strat]

    -- Goal becomes: g.isTerminal = true
    exact h_g_terminal

-- Universal theorem: every well-formed strategy terminates within literal count bound
-- This version avoids the complex shift property by using bounded iteration
theorem every_valid_strategy_terminates_quickly {Var : Type} [DecidableEq Var] :
    ∀ (formula : Formula Var) (strategy : Strategy Var),
    WellFormedStrategy strategy →
    (iterateStrategy formula strategy formula.countLiterals).isTerminal = true := by
  -- RESTRUCTURED APPROACH: Use well-founded induction on formulas
  intro formula
  -- Apply well-founded induction on the literal count ordering
  apply HasLowerLiteralCount_wellFounded.induction formula
  intro f ih strategy h_wf
  -- ih gives us: ∀ g with fewer literals than f, the property holds for g

  -- First check if f has 0 literals (base case)
  by_cases h_zero : f.countLiterals = 0
  · -- Case: f has 0 literals
    -- A formula with 0 literals must be terminal
    -- The key insight: use an existing helper theorem
    have h_terminal : f.isTerminal = true := by
      -- If countLiterals = 0, then either f = [] or f has clauses with total length 0
      -- In both cases, the formula is terminal
      cases f with
      | nil =>
        -- Empty formula is terminal
        unfold Formula.isTerminal
        simp
      | cons head tail =>
        -- Non-empty formula with 0 literals must have an empty clause
        -- Since countLiterals = sum of clause lengths = 0, at least one clause is empty
        unfold Formula.countLiterals at h_zero
        simp at h_zero
        -- After simp, h_zero is a conjunction, extract the parts
        have h_head_empty : head.length = 0 := by
          -- h_zero gives us head = [] ∧ tail sum = 0
          -- If head = [], then head.length = 0
          have h_head_nil : head = [] := h_zero.1
          rw [h_head_nil]
          simp
        -- An empty clause makes the formula terminal
        have h_clause_empty : head.isEmpty = true := by
          unfold Clause.isEmpty
          rw [List.isEmpty_iff_length_eq_zero]
          exact h_head_empty
        -- So formula has empty clause and is terminal
        unfold Formula.isTerminal Formula.hasEmptyClause
        simp
        -- Need to prove: head.isEmpty = true ∨ ∃ x ∈ tail, x.isEmpty = true
        left  -- Choose the first option: head.isEmpty = true
        exact h_clause_empty

    -- Now show the main goal: (iterateStrategy f strategy f.countLiterals).isTerminal = true
    rw [h_zero]  -- This rewrites f.countLiterals to 0
    simp [iterateStrategy]  -- iterateStrategy f strategy 0 = f
    exact h_terminal

  · -- Case: f has > 0 literals
    -- We need to show: (iterateStrategy f strategy f.countLiterals).isTerminal = true
    -- Strategy: check what the strategy says about f
    match h_strat : strategy f with
    | .Terminal h_f_terminal =>
      -- Strategy says f is terminal
      -- Then iterateStrategy will detect this and stop at any step
      -- We need a lemma: if formula is terminal, iterateStrategy preserves it
      have h_iterate_preserves : ∀ n, (iterateStrategy f strategy n).isTerminal = true := by
        intro n
        induction n with
        | zero => simp [iterateStrategy]; exact h_f_terminal
        | succ k ih_k =>
          simp [iterateStrategy]
          -- The match will see that (iterateStrategy f strategy k) is terminal
          -- So it returns the terminal formula unchanged
          have h_k_terminal : (iterateStrategy f strategy k).isTerminal = true := ih_k
          -- When a formula is terminal, strategy should return Terminal (by well-formedness)
          have ⟨h_proof, h_eq⟩ := (h_wf (iterateStrategy f strategy k)).1 h_k_terminal
          rw [h_eq]
          exact h_k_terminal
      exact h_iterate_preserves f.countLiterals

    | .Continue op h_op_applicable =>
      -- Strategy says to continue with operation op
      -- By well-formedness, f must be nonterminal
      have h_nonterminal : f.isNonterminal = true := by
        by_contra h_not_nt
        have h_terminal : f.isTerminal = true := by
          unfold Formula.isNonterminal at h_not_nt
          simp at h_not_nt
          exact h_not_nt
        have ⟨h_proof, h_eq⟩ := (h_wf f).1 h_terminal
        rw [h_eq] at h_strat
        -- This gives us Terminal = Continue, which is impossible
        have : StrategyResult.Terminal h_proof = StrategyResult.Continue op h_op_applicable := h_strat
        injection this

      -- Operation decreases literal count
      have h_decrease : (f.applyOp op).countLiterals < f.countLiterals :=
        operation_decreases_literalCount f op h_nonterminal h_op_applicable

      -- Apply IH to the smaller formula
      have h_wf_rel : HasLowerLiteralCount (f.applyOp op) f := by
        unfold HasLowerLiteralCount
        exact h_decrease

      -- The IH tells us (f.applyOp op) terminates within its literal count
      have ih_result := ih (f.applyOp op) h_wf_rel strategy h_wf
      -- ih_result : (iterateStrategy (f.applyOp op) strategy (f.applyOp op).countLiterals).isTerminal = true

      -- Now we need to connect this to iterating on f for f.countLiterals steps
      -- Key insight: f.countLiterals > (f.applyOp op).countLiterals
      -- So after 1 step on f, we have enough remaining steps

      -- We need to show: (iterateStrategy f strategy f.countLiterals).isTerminal = true
      -- Key insight: after 1 step, we get (f.applyOp op) which needs ≤ (f.applyOp op).countLiterals steps
      -- Since f.countLiterals > (f.applyOp op).countLiterals, we have enough steps

      -- First, let's understand what happens in the first step
      have h_positive : f.countLiterals > 0 := by
        -- f has > 0 literals (from h_zero)
        push_neg at h_zero
        exact Nat.pos_of_ne_zero h_zero

      -- So f.countLiterals = n + 1 for some n
      have ⟨n, h_n⟩ : ∃ n, f.countLiterals = n + 1 := by
        cases h_eq : f.countLiterals with
        | zero => rw [h_eq] at h_positive; exact absurd h_positive (Nat.lt_irrefl 0)
        | succ n => exact ⟨n, rfl⟩

      -- After 1 step, we apply the operation
      have h_first_step : iterateStrategy f strategy 1 = f.applyOp op := by
        rw [iterateStrategy_one_step]
        rw [h_strat]

      -- We have (f.applyOp op).countLiterals < f.countLiterals = n + 1
      -- So (f.applyOp op).countLiterals ≤ n
      have h_bound : (f.applyOp op).countLiterals ≤ n := by
        rw [h_n] at h_decrease
        exact Nat.lt_succ_iff.mp h_decrease

      -- The challenge: connect iterateStrategy f strategy (n+1) to the IH result
      -- Without the shift property, we need a different approach
      -- Key insight: We need a monotonicity lemma
      -- Let's prove that if we have enough steps to terminate from a smaller formula,
      -- then we have enough steps from the larger formula

      -- We know: (iterateStrategy (f.applyOp op) strategy (f.applyOp op).countLiterals).isTerminal = true
      -- We need: (iterateStrategy f strategy f.countLiterals).isTerminal = true

      -- Since f.countLiterals = n + 1 and (f.applyOp op).countLiterals ≤ n
      -- We have enough steps remaining after the first operation

      -- The key insight: we need to connect the iteration steps
      -- After 1 step from f, we get f.applyOp op (smaller formula)
      -- The IH tells us this smaller formula terminates within its literal count
      -- Since f.countLiterals = n+1 > (f.applyOp op).countLiterals, we have enough steps

      -- The core insight: we need to prove that after 1 step on f,
      -- the remaining iteration is equivalent to iterating on the smaller formula

      -- We'll prove this by showing that the smaller formula terminates within our step budget
      -- Since (f.applyOp op).countLiterals ≤ n and it terminates within its literal count,
      -- it definitely terminates within n steps

      -- Step 1: The smaller formula terminates within n steps (by monotonicity)
      have h_smaller_terminates_in_n : (iterateStrategy (f.applyOp op) strategy n).isTerminal = true := by
        apply iterateStrategy_monotonic (f.applyOp op) strategy (f.applyOp op).countLiterals n h_wf h_bound ih_result

      -- Step 2: Show f terminates within n+1 steps using a direct approach
      -- We'll use the fact that after 1 step from f, we get f.applyOp op
      -- and we know f.applyOp op terminates within n steps

      -- Key lemma: iterateStrategy f strategy (n+1) follows this pattern:
      -- 1. Apply strategy to f → Continue op (given h_strat)
      -- 2. Get f.applyOp op and continue for n more steps
      -- 3. Since we know f.applyOp op terminates in ≤ n steps, we're done

      -- The fundamental connection: Apply our core shift lemma
      -- We have everything needed for iterateStrategy_shift_step:
      -- - f and strategy
      -- - op and h_op_applicable (from the Continue case)
      -- - h_strat: strategy f = .Continue op h_op_applicable
      -- - h_smaller_terminates_in_n: smaller formula terminates in n steps

      -- Apply the shift lemma: we need to show f.countLiterals = n + 1 terminates
      -- Our shift lemma shows (n + 1) terminates, and f.countLiterals = n + 1
      rw [h_n] -- Replace f.countLiterals with n + 1
      apply iterateStrategy_shift_step f strategy op h_op_applicable n h_strat h_smaller_terminates_in_n

/-
  -- OLD APPROACH (commented out for reference)
  -- This is kept for historical reasons but will be removed once the new proof is complete
  -- The old approach used regular induction on literal count which led to issues
  -- accessing the well-founded induction hypothesis for arbitrary formulas
-/

-- Instance theorem: any specific well-formed strategy terminates within bound
theorem any_valid_strategy_terminates_quickly {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (strategy : Strategy Var)
    (h_wf : WellFormedStrategy strategy) :
    (iterateStrategy formula strategy formula.countLiterals).isTerminal = true :=
  every_valid_strategy_terminates_quickly formula strategy h_wf

-- Existential version: if you need the witness explicitly
theorem strategy_terminates_within_bound {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (strategy : Strategy Var)
    (h_wf : WellFormedStrategy strategy) :
    ∃ k ≤ formula.countLiterals, (iterateStrategy formula strategy k).isTerminal = true :=
  ⟨formula.countLiterals, Nat.le_refl _, every_valid_strategy_terminates_quickly formula strategy h_wf⟩

-- Helper lemmas for list operation proofs
section ListOperationHelpers

/--
**Zero Literals Terminal**: A formula with zero literals is always terminal.

This key lemma bridges literal count tracking to termination detection.
A formula with 0 literals either has no clauses (satisfiable) or
has empty clauses (unsatisfiable) - both are terminal states.
-/
lemma zero_literals_terminal {Var : Type} (formula : Formula Var)
    (h_zero : formula.countLiterals = 0) : formula.isTerminal = true := by
  -- Proof extracted from main theorem base case (lines 305-329)
  -- If countLiterals = 0, then either f = [] or f has clauses with total length 0
  -- In both cases, the formula is terminal
  cases formula with
  | nil =>
    -- Empty formula is terminal
    unfold Formula.isTerminal
    simp
  | cons head tail =>
    -- Non-empty formula with 0 literals must have an empty clause
    -- Since countLiterals = sum of clause lengths = 0, at least one clause is empty
    unfold Formula.countLiterals at h_zero
    simp at h_zero
    -- After simp, h_zero is a conjunction, extract the parts
    have h_head_empty : head.length = 0 := by
      -- h_zero gives us head = [] ∧ tail sum = 0
      -- If head = [], then head.length = 0
      have h_head_nil : head = [] := h_zero.1
      rw [h_head_nil]
      simp
    -- An empty clause makes the formula terminal
    have h_clause_empty : head.isEmpty = true := by
      unfold Clause.isEmpty
      rw [List.isEmpty_iff_length_eq_zero]
      exact h_head_empty
    -- So formula has empty clause and is terminal
    unfold Formula.isTerminal Formula.hasEmptyClause
    simp
    -- Need to prove: head.isEmpty = true ∨ ∃ x ∈ tail, x.isEmpty = true
    left  -- Choose the first option: head.isEmpty = true
    exact h_clause_empty

/--
**Literal Count Progression**: If we apply k operations without reaching a terminal state,
the literal count decreases by at least k.

This is the key lemma that tracks literal count through sequential operations,
ensuring we can't exceed the original literal count bound.
-/
lemma literal_count_progression {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var)) (k : Nat)
    (h_k_bound : k ≤ ops.length)
    (h_valid : ∀ i (h_bound : i < ops.length), (ops.get ⟨i, h_bound⟩).IsApplicable (formula.applyOps (ops.take i)))
    (h_no_term : ∀ i < k, ¬(formula.applyOps (ops.take i)).isTerminal = true) :
    (formula.applyOps (ops.take k)).countLiterals ≤ formula.countLiterals - k := by
  -- Use induction on k to track literal count decrease
  induction k with
  | zero =>
    -- Base case: k = 0, no operations applied
    simp [Formula.applyOps]
  | succ n ih =>
    -- Inductive step: prove for n+1 given result for n
    -- IH: (formula.applyOps (ops.take n)).countLiterals ≤ formula.countLiterals - n
    -- Goal: (formula.applyOps (ops.take (n+1))).countLiterals ≤ formula.countLiterals - (n+1)

    -- First, ensure we have the bounds we need
    have h_n_bound : n ≤ ops.length := Nat.le_of_succ_le h_k_bound
    have h_succ_bound : n < ops.length := Nat.lt_of_succ_le h_k_bound

    -- Get the intermediate formula after n steps
    let intermediate := formula.applyOps (ops.take n)

    -- By h_no_term, intermediate is not terminal
    have h_intermediate_nonterm : intermediate.isNonterminal = true := by
      have h_not_term : ¬intermediate.isTerminal = true := h_no_term n (Nat.lt_succ_self n)
      unfold Formula.isNonterminal
      simp [h_not_term]

    -- Get the operation to apply at step n
    let op := ops.get ⟨n, h_succ_bound⟩

    -- This operation is applicable to intermediate by h_valid
    have h_op_applicable : op.IsApplicable intermediate := by
      have h_valid_n := h_valid n h_succ_bound
      -- Need to show that ops.get ⟨n, h_succ_bound⟩ is applicable to formula.applyOps (ops.take n)
      -- These are definitionally equal by our definitions
      exact h_valid_n

    -- Applying op to intermediate decreases literal count
    have h_decrease : (intermediate.applyOp op).countLiterals < intermediate.countLiterals :=
      operation_decreases_literalCount intermediate op h_intermediate_nonterm h_op_applicable

    -- Connect to our goal: applying n+1 operations equals applying n operations then one more
    have h_take_succ : formula.applyOps (ops.take (n + 1)) = intermediate.applyOp op := by
      -- This follows directly from the sequential nature of list operations
      -- We can use our existing pattern similar to applyOps_take_cons_succ

      -- Key insight: ops.take (n+1) can be split as ops.take n followed by ops[n]
      -- This allows us to apply the sequential operation property

      -- Apply Formula.applyOps definition and use list properties
      unfold Formula.applyOps intermediate op

      -- The goal is now: List.foldl Formula.applyOp formula (ops.take (n + 1)) =
      --                  (List.foldl Formula.applyOp formula (ops.take n)).applyOp (ops.get ⟨n, h_succ_bound⟩)

      -- This is exactly the pattern that List.foldl follows when processing one more element
      -- We can establish this using the definition of take with successive indices

      -- Use induction on the structure or establish via list lemmas
      -- For now, this follows from the fundamental property of list foldl with consecutive takes
      -- The mathematical pattern is exactly what our existing lemma applyOps_take_cons_succ establishes

      -- The goal is: formula.applyOps (ops.take (n + 1)) = intermediate.applyOp op
      -- where intermediate = formula.applyOps (ops.take n) and op = ops.get ⟨n, h_succ_bound⟩

      -- We can prove this using the fundamental property of sequential list operations
      -- The key insight: ops.take (n+1) is equivalent to taking n elements plus the (n+1)th element

      -- For a direct proof, we'd use list properties like:
      -- ops.take (n+1) = ops.take n ++ [ops.get n] (when n < ops.length)
      -- And then applyOps distributes over concatenation

      -- This follows from our existing pattern in applyOps_take_cons_succ
      -- but requires adapting it to the general case rather than cons structure

      -- The proof would unfold Formula.applyOps, use List.foldl properties,
      -- and apply the list concatenation structure

      -- The goal is to show: formula.applyOps (ops.take (n + 1)) = intermediate.applyOp op
      -- where: intermediate = formula.applyOps (ops.take n) and op = ops.get ⟨n, h_succ_bound⟩

      -- Key insight: this follows from properties of List.take and List.foldl
      -- We need ops.take (n + 1) to include exactly ops.take n plus the element at position n

      -- Since n < ops.length, we can decompose the list at position n
      -- The take (n + 1) includes exactly the first n elements plus the nth element

      unfold Formula.applyOps

      -- Use the fact that take (n + 1) = take n + [ops[n]] when n < ops.length
      -- This requires careful handling of list indexing and concatenation

      -- We can use induction on the list structure or direct properties of take/foldl
      -- The mathematical content is well-established in list theory

      -- Apply list theory for take/foldl relationship
      have h_take_structure : ops.take (n + 1) = ops.take n ++ [ops.get ⟨n, h_succ_bound⟩] := by
        -- Use mathlib theorem: take_concat_get'
        rw [← List.take_concat_get' ops n h_succ_bound]
        -- Show that ops[n] = ops.get ⟨n, h_succ_bound⟩
        congr

      rw [h_take_structure]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

    -- Apply the inductive hypothesis and operation decrease
    rw [h_take_succ]

    -- We know intermediate.countLiterals ≤ formula.countLiterals - n (by IH)
    have h_ih_result : intermediate.countLiterals ≤ formula.countLiterals - n := by
      apply ih h_n_bound
      -- Need to show ∀ i < n, ¬(formula.applyOps (ops.take i)).isTerminal = true
      intro i h_i_lt_n
      exact h_no_term i (Nat.lt_trans h_i_lt_n (Nat.lt_succ_self n))

    -- We know (intermediate.applyOp op).countLiterals < intermediate.countLiterals
    -- Combined with IH: (intermediate.applyOp op).countLiterals < formula.countLiterals - n
    -- We need: (intermediate.applyOp op).countLiterals ≤ formula.countLiterals - (n + 1)
    -- This follows from natural number arithmetic with strict decrease
    have h_strict_bound : (intermediate.applyOp op).countLiterals < formula.countLiterals - n :=
      Nat.lt_of_lt_of_le h_decrease h_ih_result

    -- For natural numbers: if x < y - n, then x ≤ y - (n + 1) when y > n
    -- This is the key arithmetic step combining strict decrease with inductive bound
    have h_final : (intermediate.applyOp op).countLiterals ≤ formula.countLiterals - (n + 1) := by
      -- We have: (intermediate.applyOp op).countLiterals < intermediate.countLiterals ≤ formula.countLiterals - n
      -- Goal: (intermediate.applyOp op).countLiterals ≤ formula.countLiterals - (n + 1)

      -- The mathematical insight: strict decrease by 1 step + inductive bound gives us the stronger bound
      -- If count decreases and we had bound ≤ original - n, then we get ≤ original - (n+1)
      -- This is a fundamental arithmetic property for termination arguments

      -- We have: (intermediate.applyOp op).countLiterals < formula.countLiterals - n
      have h_strict_final : (intermediate.applyOp op).countLiterals < formula.countLiterals - n :=
        Nat.lt_of_lt_of_le h_decrease h_ih_result

      -- For natural numbers: if x < y - n, then x ≤ y - (n + 1) provided y ≥ n + 1
      -- This follows from: x < y - n = (y - (n + 1)) + 1, so x ≤ y - (n + 1)

      -- Simple approach: use the transitivity and properties of strict decrease
      -- We know that each operation decreases by at least 1, so n+1 operations decrease by at least n+1
      -- This is a fundamental property of our termination argument

      -- The key insight: if x < intermediate ≤ original - n, then x ≤ original - (n+1)
      -- This is because operations decrease count, and we compound the decreases

      -- For practical purposes, this arithmetic follows from the core termination properties
      -- and the inductive structure we've established

      -- Natural number arithmetic: if x < y - n, then x ≤ y - (n+1)
      -- Use the fact that strict inequality gives us the stronger bound
      have h_le_pred : (intermediate.applyOp op).countLiterals ≤ (formula.countLiterals - n) - 1 := by
        -- x < y implies x ≤ y - 1 for natural numbers
        exact Nat.le_sub_one_of_lt h_strict_final
      -- Show that (y - n) - 1 = y - (n + 1)
      have h_sub_rearrange : (formula.countLiterals - n) - 1 = formula.countLiterals - (n + 1) := by
        rw [← Nat.sub_sub]
      -- Combine via transitivity
      rw [← h_sub_rearrange]
      exact h_le_pred

    exact h_final

end ListOperationHelpers

-- Extension to finite operation sequences
section ListOperations

/-- Result type for termination search that explicitly carries semantic information -/
inductive TerminationSearchResult {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var)) : Type where
  | Found (k : Nat) :
      (h_bound : k ≤ min ops.length formula.countLiterals) →
      (h_terminal : (formula.applyOps (ops.take k)).isTerminal = true) →
      TerminationSearchResult formula ops
  | Exhausted (k : Nat) :
      (h_bound : k ≤ min ops.length formula.countLiterals) →
      (h_eq : k = ops.length) →
      (h_no_term : ∀ i ≤ k, ¬(formula.applyOps (ops.take i)).isTerminal = true) →
      TerminationSearchResult formula ops

noncomputable def any_valid_operation_list_terminates_within_bound {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var))
    (h_valid : ∀ i (h_bound : i < ops.length), (ops.get ⟨i, h_bound⟩).IsApplicable (formula.applyOps (ops.take i))) :
    TerminationSearchResult formula ops := by
  -- Strategy: Use helper lemmas to track literal count and detect termination
  -- Key insight: Either we find termination early or literal count forces termination

  -- Base case: if formula is already terminal
  by_cases h_term_start : formula.isTerminal = true
  · -- Case: formula is already terminal at step 0
    exact TerminationSearchResult.Found 0 (by simp) (by simp [Formula.applyOps, h_term_start])
  · -- Case: formula is nonterminal, so we track operations until termination

    -- Key insight: Use bounded search up to min(ops.length, formula.countLiterals)
    let bound := min ops.length formula.countLiterals

    -- Search for first termination point within bound
    -- This is a finite search since bound is finite
    have h_bound_finite : bound ≤ ops.length ∧ bound ≤ formula.countLiterals := by
      constructor
      · -- bound ≤ ops.length
        simp [bound]
        exact Nat.min_le_left ops.length formula.countLiterals
      · -- bound ≤ formula.countLiterals
        simp [bound]
        exact Nat.min_le_right ops.length formula.countLiterals

    -- Core argument: Within bound steps, either:
    -- 1. We find early termination, or
    -- 2. Literal count reaches 0, forcing termination by zero_literals_terminal

    -- For the implementation, we use the mathematical insight:
    -- If we don't find early termination in bound steps, then by literal_count_progression,
    -- the literal count would be ≤ original - bound ≤ original - formula.countLiterals = 0
    -- By zero_literals_terminal, literal count 0 implies terminal

    -- The detailed proof requires careful case analysis on the search process
    -- This is exactly the pattern our helper lemmas were designed to support
    by_cases h_short_ops : ops.length ≤ formula.countLiterals
    · -- Case: ops.length ≤ formula.countLiterals, so min = ops.length
      -- In this case, we need to check for termination up to ops.length
      have h_bound_eq : bound = ops.length := by
        simp [bound, Nat.min_eq_left h_short_ops]

      -- Check if there's termination anywhere up to ops.length
      by_cases h_term_exists : ∃ i ≤ ops.length, (formula.applyOps (ops.take i)).isTerminal = true
      · -- Termination exists: find and return it
        let i := Classical.choose h_term_exists
        have h_i_bound : i ≤ ops.length := (Classical.choose_spec h_term_exists).1
        have h_i_term : (formula.applyOps (ops.take i)).isTerminal = true := (Classical.choose_spec h_term_exists).2
        have h_i_min : i ≤ min ops.length formula.countLiterals := by
          simp [Nat.min_eq_left h_short_ops]
          exact h_i_bound
        exact TerminationSearchResult.Found i h_i_min h_i_term
      · -- No termination exists: return exhaustion
        push_neg at h_term_exists
        have h_ops_bound : ops.length ≤ min ops.length formula.countLiterals := by
          rw [Nat.min_eq_left h_short_ops]
        -- h_term_exists now provides exactly what we need:
        -- ∀ i ≤ ops.length, ¬(formula.applyOps (ops.take i)).isTerminal = true
        exact TerminationSearchResult.Exhausted ops.length h_ops_bound rfl h_term_exists
    · -- Case: formula.countLiterals < ops.length, so min = formula.countLiterals
      push_neg at h_short_ops
      have h_formula_lt : formula.countLiterals < ops.length := h_short_ops
      have h_bound_eq : bound = formula.countLiterals := by
        simp [bound, Nat.min_eq_right (Nat.le_of_lt h_formula_lt)]
      -- In this case, we need to check if there's early termination before formula.countLiterals
      -- If so, return that early termination point; otherwise, termination is forced at formula.countLiterals

      -- First check: is there early termination?
      by_cases h_early_term : ∃ i < formula.countLiterals, (formula.applyOps (ops.take i)).isTerminal = true
      · -- Case: early termination exists
        let i := Classical.choose h_early_term
        have h_i_lt : i < formula.countLiterals := (Classical.choose_spec h_early_term).1
        have h_i_terminal : (formula.applyOps (ops.take i)).isTerminal = true := (Classical.choose_spec h_early_term).2
        -- Return i as our witness
        have h_i_bound : i ≤ min ops.length formula.countLiterals := by
          -- Since i < formula.countLiterals and formula.countLiterals = min(ops.length, formula.countLiterals)
          rw [Nat.min_eq_right (Nat.le_of_lt h_formula_lt)]
          exact Nat.le_of_lt h_i_lt
        exact TerminationSearchResult.Found i h_i_bound h_i_terminal

      · -- Case: no early termination
        -- Then termination is forced at formula.countLiterals
        push_neg at h_early_term
        have h_formula_bound : formula.countLiterals ≤ min ops.length formula.countLiterals := by
          -- Since formula.countLiterals < ops.length, min = formula.countLiterals
          rw [Nat.min_eq_right (Nat.le_of_lt h_formula_lt)]
        exact TerminationSearchResult.Found formula.countLiterals h_formula_bound (by
                 -- Since no early termination up to formula.countLiterals,
                 -- we can apply literal_count_progression
                 have h_literal_decrease : (formula.applyOps (ops.take formula.countLiterals)).countLiterals ≤ formula.countLiterals - formula.countLiterals := by
                   apply literal_count_progression
                   · exact Nat.le_of_lt h_formula_lt
                   · exact h_valid
                   · exact h_early_term

                 -- This gives us literal count = 0
                 have h_zero_literals : (formula.applyOps (ops.take formula.countLiterals)).countLiterals = 0 := by
                   rw [Nat.sub_self] at h_literal_decrease
                   exact Nat.eq_zero_of_le_zero h_literal_decrease

                 -- Apply zero_literals_terminal
                 exact zero_literals_terminal (formula.applyOps (ops.take formula.countLiterals)) h_zero_literals)


/-- Corollary: Any valid finite operation sequence either terminates or gets exhausted -/
theorem any_valid_operation_list_terminates_or_exhausts {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (ops : List (FormulaOp Var))
    (h_valid : ∀ i (h_bound : i < ops.length), (ops.get ⟨i, h_bound⟩).IsApplicable (formula.applyOps (ops.take i))) :
    (∃ k ≤ ops.length, (formula.applyOps (ops.take k)).isTerminal = true) ∨
    (ops.length ≤ formula.countLiterals ∧ ¬(formula.applyOps ops).isTerminal = true) := by
  -- This corollary follows from the main theorem through logical case analysis
  -- The mathematical insight: either early termination or bounded exhaustion

  -- Apply the main theorem to get our fundamental result
  have result := any_valid_operation_list_terminates_within_bound formula ops h_valid

  -- The main theorem now gives us a TerminationSearchResult
  -- We need to derive our specific disjunctive conclusion

  cases result with
  | Found k h_k_bound h_terminal =>
    -- Case: termination found at position k
    -- Check if this satisfies the corollary's first disjunct: k ≤ ops.length
    have h_k_le_ops : k ≤ ops.length := Nat.le_trans h_k_bound (Nat.min_le_left _ _)
    -- We have termination, so we return the first disjunct
    exact Or.inl ⟨k, h_k_le_ops, h_terminal⟩
  | Exhausted k h_k_bound h_eq h_no_term =>
    -- Case: exhaustion without early termination (k = ops.length)
    -- We prove the second disjunct: (ops.length ≤ formula.countLiterals ∧ ¬(formula.applyOps ops).isTerminal = true)

    -- First part: ops.length ≤ formula.countLiterals
    have h_length_bound : ops.length ≤ formula.countLiterals := by
      rw [←h_eq]
      exact Nat.le_trans h_k_bound (Nat.min_le_right _ _)

    -- Second part: ¬(formula.applyOps ops).isTerminal = true
    have h_final_nonterm : ¬(formula.applyOps ops).isTerminal = true := by
      -- From h_no_term: ∀ i ≤ k, ¬(formula.applyOps (ops.take i)).isTerminal = true
      -- Since k = ops.length, we have ∀ i ≤ ops.length, ¬(formula.applyOps (ops.take i)).isTerminal = true
      -- In particular, for i = ops.length: ¬(formula.applyOps (ops.take ops.length)).isTerminal = true
      -- Since ops.take ops.length = ops, this gives us ¬(formula.applyOps ops).isTerminal = true
      have h_at_length : ¬(formula.applyOps (ops.take ops.length)).isTerminal = true := by
        apply h_no_term
        rw [h_eq]
      rwa [List.take_length] at h_at_length

    exact Or.inr ⟨h_length_bound, h_final_nonterm⟩

end ListOperations

