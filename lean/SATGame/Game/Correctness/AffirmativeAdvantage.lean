import SATGame.Game.Basic
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.FormulaOps.Termination.SetVariable
import SATGame.FormulaOps.Termination.RemoveClause
import SATGame.FormulaOps.SatisfiabilityPreservation
import SATGame.Game.Correctness.StrategyExistence
import SATGame.CNF.Satisfiability

/-!
# Affirmative Advantage

This module proves that Affirmative can win from any satisfiable formula,
using the concept of "AffMoveRounds" - cycles where Affirmative makes one move
followed by zero or more Negative responses.

## Main Results

1. `aff_move_round_preservation`: Affirmative can maintain satisfiability through any round
2. `satisfiable_implies_affirmative_victory`: Affirmative has a winning strategy from any satisfiable formula

## Key Insight

Empty formulas are satisfiable (vacuously true), so preserving satisfiability automatically
covers both the case where the game continues and where Affirmative wins immediately.

## Key Concept

An **AffMoveRound** consists of:
- One `setVariable` operation by Affirmative
- Zero or more `removeClause` operations by Negative in response

Affirmative's strategy: Use strategy existence results to choose preserving setVariable moves.
The proof relies on position preservation to show Negative's removeClause moves can't break satisfiability.
-/


/-!
## Helper Theorems
-/

/-- Valid AffMoveRound operations decrease literal count -/
theorem aff_move_round_decreases_literals {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (round : AffMoveRound Var)
    (h_nonterminal : formula.isNonterminal = true)
    (h_aff_valid : round.aff_move.IsApplicable formula)
    (h_neg_valid : valid_clause_removal_sequence (formula.applyOp round.aff_move) round.neg_response) :
    (apply_aff_move_round formula round).countLiterals < formula.countLiterals ∨
    (apply_aff_move_round formula round).isTerminal := by
  unfold apply_aff_move_round

  let after_aff := formula.applyOp round.aff_move

  -- Case analysis: is the formula terminal after Affirmative's move?
  by_cases h_aff_terminal : after_aff.isTerminal

  · -- Case 1: Affirmative's move made formula terminal → We're done!
    right
    -- If after_aff is terminal, then only empty sequence can be valid for Negative
    have h_neg_empty : round.neg_response = [] := by
      -- If after_aff is terminal, then no further moves are valid (nonterminal requirement fails)
      have h_no_valid_moves : ∀ (ops : List (FormulaOp Var)), ¬valid_clause_removal_sequence after_aff ops ∨ ops = [] := by
        intro ops
        by_cases h_empty : ops = []
        · right; exact h_empty
        · left
          intro h_valid
          cases h_valid with
          | nil => simp at h_empty
          | cons h_nonterminal _ _ _ =>
            have h_not_terminal : ¬after_aff.isTerminal := by
              have h_eq : after_aff.isTerminal = false := by
                rw [Formula.isNonterminal] at h_nonterminal
                simp at h_nonterminal
                exact h_nonterminal
              rw [h_eq]
              simp
            exact h_not_terminal h_aff_terminal
      have h_no_valid := h_no_valid_moves round.neg_response
      cases h_no_valid with
      | inl h_not_valid => exfalso; exact h_not_valid h_neg_valid
      | inr h_empty => exact h_empty

    -- With empty neg_response, the result is just after_aff
    simp [h_neg_empty, List.foldl_nil]
    exact h_aff_terminal

  · -- Case 2: Affirmative's move didn't make formula terminal
    -- Then it decreased literal count, and Negative's moves decrease further
    left

    -- Affirmative's move decreases literals (from Phase 1 termination theorems)
    have h_aff_decreases : after_aff.countLiterals < formula.countLiterals := by
      cases h_aff_move : round.aff_move with
      | SetVariable var value =>
        have h_after_aff : after_aff = formula.setVariable var value := by
          unfold after_aff
          rw [h_aff_move]
          unfold Formula.applyOp
          rfl
        rw [h_after_aff]
        apply setVariable_decreases_literalCount formula var value h_nonterminal
        -- Extract the variable containment from h_aff_valid
        have h_contains : formula.containsVariable var = true := by
          rw [h_aff_move] at h_aff_valid
          unfold FormulaOp.IsApplicable at h_aff_valid
          simp at h_aff_valid
          exact h_aff_valid
        exact h_contains
      | RemoveClause index =>
        have h_after_aff : after_aff = formula.removeClause index := by
          unfold after_aff
          rw [h_aff_move]
          unfold Formula.applyOp
          rfl
        rw [h_after_aff]
        apply removeClause_decreases_literalCount formula index h_nonterminal
        -- Extract the index bound from h_aff_valid
        have h_index_bound : index < formula.length := by
          rw [h_aff_move] at h_aff_valid
          unfold FormulaOp.IsApplicable at h_aff_valid
          simp at h_aff_valid
          exact h_aff_valid
        exact h_index_bound

    -- Negative's moves can only decrease literal count further (removeClause ≤)
    have h_neg_nonincreasing : (round.neg_response.foldl Formula.applyOp after_aff).countLiterals ≤ after_aff.countLiterals := by
      -- Use the general theorem about clause removal sequences being nonincreasing
      apply clause_removal_sequence_nonincreasing after_aff round.neg_response
      -- All operations in neg_response are removeClause operations (from h_neg_valid)
      exact valid_clause_removal_sequence_all_removes after_aff round.neg_response h_neg_valid

    -- Overall: strictly less than original
    apply Nat.lt_of_le_of_lt h_neg_nonincreasing h_aff_decreases


/-!
## Main Theorems
-/

/--
**Single Round Preservation**: If Affirmative starts with a satisfiable, nonterminal formula,
they can choose a move such that after any valid Negative response, the result is still satisfiable.
Note: Empty formulas are satisfiable, so this covers the case where Affirmative wins immediately.
-/
theorem aff_move_round_preservation {Var : Type} [DecidableEq Var] (formula : Formula Var)
    (h_satisfiable : formula.IsSatisfiable)
    (h_nonterminal : formula.isNonterminal = true) :
    ∃ (aff_move : FormulaOp Var),
      aff_move.IsApplicable formula ∧
      ∀ (neg_response : List (FormulaOp Var)),
        valid_clause_removal_sequence (formula.applyOp aff_move) neg_response →
        let post_round := (neg_response.foldl Formula.applyOp (formula.applyOp aff_move))
        post_round.IsSatisfiable := by
  -- Affirmative has a preserving setVariable move
  obtain ⟨var, value, h_var_in_formula, h_preserves_sat⟩ :=
    satisfiable_has_preserving_setVariable formula h_satisfiable h_nonterminal

  -- The move is setVariable var value
  let aff_move := FormulaOp.SetVariable var value
  exists aff_move

  constructor
  · -- Show aff_move is applicable
    unfold FormulaOp.IsApplicable
    exact h_var_in_formula

  · -- Show the preservation property
    intro neg_response h_valid_response

    -- After Affirmative's move, formula is still satisfiable
    have h_after_aff_sat : (formula.applyOp aff_move).IsSatisfiable := by
      unfold Formula.applyOp aff_move
      simp
      exact h_preserves_sat

    -- Negative's response preserves satisfiability
    exact valid_clause_removal_sequence_preserves_satisfiability (formula.applyOp aff_move) h_after_aff_sat h_valid_response

-- Note: assignment_following_strategy is now defined in Game/Basic.lean

/--
**Terminal Formula Contradiction**: Terminal formulas with empty clauses cannot be satisfiable.

This captures the fundamental impossibility: if a formula has reached a terminal state
with an empty clause, no assignment can satisfy the empty clause.
-/
theorem terminal_with_empty_clause_unsatisfiable {Var : Type} [DecidableEq Var] (formula : Formula Var)
    (_ : formula.isTerminal = true)
    (h_has_empty : formula.hasEmptyClause = true) :
    ¬formula.IsSatisfiable := by
  intro h_sat
  obtain ⟨local_assignment, h_local_assignment_satisfies⟩ := h_sat
  unfold Formula.hasEmptyClause at h_has_empty
  rw [List.any_eq_true] at h_has_empty
  obtain ⟨empty_clause, h_empty_in_formula, h_empty_clause_isEmpty⟩ := h_has_empty
  unfold Formula.satisfiedByAssignment at h_local_assignment_satisfies
  rw [List.all_eq_true] at h_local_assignment_satisfies
  have h_empty_satisfied := h_local_assignment_satisfies empty_clause h_empty_in_formula
  unfold Clause.satisfiedByAssignment at h_empty_satisfied
  unfold Clause.isEmpty at h_empty_clause_isEmpty
  rw [List.isEmpty_iff] at h_empty_clause_isEmpty
  rw [h_empty_clause_isEmpty] at h_empty_satisfied
  simp at h_empty_satisfied

/--
**Assignment Strategy Preserves Satisfiability**: The assignment-following strategy preserves satisfiability.

When applied to a formula satisfied by the given assignment, the resulting formula
after the strategy move is also satisfiable.
-/
theorem assignment_strategy_preserves_satisfiability_nonterminal {Var : Type} [DecidableEq Var] [Inhabited Var]
    (formula : Formula Var) (assignment : Assignment Var)
    (h_nonterminal : formula.isNonterminal = true)
    (h_satisfies : formula.satisfiedByAssignment assignment = true) :
    let after_move := formula.applyOp (assignment_following_strategy assignment formula)
    after_move.IsSatisfiable := by
  -- Since formula is nonterminal, assignment_following_strategy sets a variable from the formula
  unfold assignment_following_strategy

  -- Convert nonterminal to not terminal for if-statement
  have h_terminal_false : formula.isTerminal = false := by
    have : formula.isNonterminal = true := h_nonterminal
    unfold Formula.isNonterminal at this
    simp at this
    exact this

  simp [h_terminal_false]

  -- Use the nonterminal hypothesis directly
  let var := Classical.choose (nonterminal_contains_variable formula h_nonterminal)
  simp [Formula.applyOp]
  exact ⟨assignment, setVariable_preserves_satisfiability_under_witness formula assignment var h_satisfies⟩



/-!
## Helper Lemmas for Assignment Strategy Victory
-/

/-- Game reaches terminal always ends at a terminal formula -/
lemma game_reaches_terminal_implies_terminal {Var : Type} [DecidableEq Var]
    (strategy : @AffirmativeStrategy Var _) (initial final : Formula Var)
    (h_reaches : game_reaches_terminal strategy initial final) :
    final.isTerminal = true := by
  induction h_reaches with
  | terminal f h_term => exact h_term
  | step h_not_terminal h_aff_move neg_moves h_neg_valid h_neg_apply h_rest ih => exact ih

/--
**Negative Moves Preserve Satisfiability**: Valid clause removal sequences preserve satisfiability.
-/
theorem negative_moves_preserve_satisfiability {Var : Type} [DecidableEq Var]
    (g : Formula Var) (assignment : Assignment Var) (neg_moves : List (FormulaOp Var))
    (h_satisfies : g.satisfiedByAssignment assignment = true)
    (h_valid : valid_clause_removal_sequence g neg_moves) :
    (neg_moves.foldl Formula.applyOp g).satisfiedByAssignment assignment = true := by
  -- We'll prove by induction on the valid clause removal sequence
  -- Key insight: clause removal never changes variables, so if assignment satisfies g,
  -- it also satisfies any formula obtained by removing clauses from g
  induction h_valid with
  | nil =>
    -- Base case: empty sequence, formula unchanged
    simp [List.foldl]
    exact h_satisfies
  | cons h_nonterminal h_is_remove h_applicable h_rest_valid ih =>
    -- Inductive case: one removal operation followed by rest
    simp [List.foldl]
    -- Apply induction hypothesis to the rest of the sequence
    apply ih
    -- Show that single clause removal preserves satisfiability by the assignment
    -- h_is_remove guarantees it's a RemoveClause operation
    obtain ⟨index, h_op_eq⟩ := h_is_remove
    rw [h_op_eq]
    simp [Formula.applyOp]
    -- Removing a clause preserves satisfiability by any assignment that satisfied the original formula
    -- This follows from the fact that removing clauses can only make formulas easier to satisfy
    unfold Formula.satisfiedByAssignment at h_satisfies ⊢
    unfold Formula.removeClause
    simp [List.eraseIdx_subset]
    -- If assignment satisfies all clauses in formula, it satisfies all clauses in formula.eraseIdx index
    intro clause h_clause_in_erased
    have h_clause_in_orig := List.mem_of_mem_eraseIdx h_clause_in_erased
    -- h_satisfies has form: (List.all formula✝ fun clause => clause.satisfiedByAssignment assignment) = true
    rw [List.all_eq_true] at h_satisfies
    exact h_satisfies clause h_clause_in_orig

/-- Assignment strategy preserves satisfaction by the original assignment throughout game execution -/
lemma assignment_strategy_preserves_assignment_satisfaction {Var : Type} [DecidableEq Var] [Inhabited Var]
    (initial final : Formula Var) (assignment : Assignment Var)
    (h_satisfies : initial.satisfiedByAssignment assignment = true)
    (h_reaches : game_reaches_terminal (assignment_to_strategy assignment) initial final) :
    final.satisfiedByAssignment assignment = true := by
  -- Use generalized induction to prove that satisfaction is preserved throughout the game
  suffices h_general : ∀ (start finish : Formula Var),
    start.satisfiedByAssignment assignment = true →
    game_reaches_terminal (assignment_to_strategy assignment) start finish →
    finish.satisfiedByAssignment assignment = true
    from h_general initial final h_satisfies h_reaches

  intro start finish h_start_satisfied h_start_to_finish
  induction h_start_to_finish with
  | terminal f h_terminal =>
    -- Base case: start = finish, so satisfaction is trivially preserved
    exact h_start_satisfied
  | @step f g h final h_not_terminal h_aff_move neg_moves h_neg_valid h_neg_apply h_rest ih =>
    -- Step case: We have f -[aff]-> g -[neg]-> h -[rest]-> final
    -- IH: h.satisfiedByAssignment assignment = true → final.satisfiedByAssignment assignment = true
    -- Goal: final.satisfiedByAssignment assignment = true
    -- We have: f.satisfiedByAssignment assignment = true (this is h_start_satisfied!)

    -- Step 1: g is satisfied (assignment strategy preserves satisfaction)
    have h_g_satisfied : g.satisfiedByAssignment assignment = true := by
      rw [h_aff_move]
      unfold assignment_to_strategy
      simp
      have h_f_nonterminal : f.isNonterminal = true := by
        unfold Formula.isNonterminal
        simp [h_not_terminal]
      let var := Classical.choose (nonterminal_contains_variable f h_f_nonterminal)
      exact setVariable_preserves_satisfiability_under_witness f assignment var h_start_satisfied

    -- Step 2: h is satisfied (negative moves preserve satisfaction)
    have h_h_satisfied : h.satisfiedByAssignment assignment = true := by
      rw [h_neg_apply]
      exact negative_moves_preserve_satisfiability g assignment neg_moves h_g_satisfied h_neg_valid

    -- Step 3: Apply IH to get final is satisfied
    exact ih h_h_satisfied

/--
**Assignment Strategy Eventually Reaches Empty**: From any satisfiable formula, the assignment
strategy constructively reaches the empty formula.

This is the key constructive theorem that builds the actual winning game sequence.
-/
theorem assignment_strategy_reaches_empty {Var : Type} [DecidableEq Var] [Inhabited Var]
    (initial : Formula Var) (assignment : Assignment Var)
    (h_satisfies : initial.satisfiedByAssignment assignment = true) :
    game_reaches_terminal (assignment_to_strategy assignment) initial [] := by
  -- We prove by well-founded induction on literal count
  -- Base case: if initial is terminal, it must be empty (since it's satisfiable)
  -- Inductive case: make progress and apply IH

  -- Use strong induction on the literal count
  suffices ∀ (n : Nat) (f : Formula Var),
    f.countLiterals ≤ n →
    f.satisfiedByAssignment assignment = true →
    game_reaches_terminal (assignment_to_strategy assignment) f []
    from this initial.countLiterals initial (le_refl _) h_satisfies

  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f h_count_le h_f_satisfies

    -- Case analysis: is f terminal?
    by_cases h_terminal : f.isTerminal

    · -- Terminal case: f must be empty
      cases terminal_formula_classification f h_terminal with
      | inl h_empty =>
        -- f is empty, so we're done
        rw [h_empty]
        have h_empty_terminal : Formula.isTerminal ([] : Formula Var) = true := by
          unfold Formula.isTerminal
          simp [List.isEmpty]
        exact game_reaches_terminal.terminal [] h_empty_terminal
      | inr h_has_empty =>
        -- f has empty clause - contradiction with satisfiability
        exfalso
        exact terminal_with_empty_clause_unsatisfiable f h_terminal h_has_empty ⟨assignment, h_f_satisfies⟩

    · -- Nonterminal case: apply strategy and use induction
      -- Convert the hypothesis to the right form
      have h_not_terminal : f.isTerminal = false := by
        cases h_term : f.isTerminal with
        | true => contradiction
        | false => rfl

      -- Apply assignment strategy to get g
      let g := f.applyOp ((assignment_to_strategy assignment).strategy f h_not_terminal).val

      -- g is still satisfiable by the same assignment
      have h_g_satisfies : g.satisfiedByAssignment assignment = true := by
        -- The assignment strategy sets a variable to its assignment value
        unfold g assignment_to_strategy
        simp
        -- Extract the variable that gets set
        have h_nonterminal_f : f.isNonterminal = true := by
          unfold Formula.isNonterminal
          simp [h_not_terminal]
        let var := Classical.choose (nonterminal_contains_variable f h_nonterminal_f)
        -- Setting var to assignment var preserves satisfaction by assignment
        exact setVariable_preserves_satisfiability_under_witness f assignment var h_f_satisfies

      -- Apply empty negative response (Negative passes)
      let h := ([] : List (FormulaOp Var)).foldl Formula.applyOp g
      have h_h_eq : h = g := by rfl
      have h_h_satisfies : h.satisfiedByAssignment assignment = true := by
        rw [h_h_eq]; exact h_g_satisfies

      -- Show that valid clause removal sequence holds for empty list
      have h_neg_valid : valid_clause_removal_sequence g [] := valid_clause_removal_sequence.nil

      -- We need to show progress: h.countLiterals < f.countLiterals
      have h_progress : h.countLiterals < f.countLiterals := by
        -- h = g and g is result of setVariable, which decreases literal count
        rw [h_h_eq]
        unfold g
        -- Extract the SetVariable operation details
        have h_nonterminal_f : f.isNonterminal = true := by
          unfold Formula.isNonterminal
          simp [h_not_terminal]
        let var := Classical.choose (nonterminal_contains_variable f h_nonterminal_f)
        have h_contains := Classical.choose_spec (nonterminal_contains_variable f h_nonterminal_f)
        -- Apply setVariable decreases literal count theorem
        apply setVariable_decreases_literalCount f var (assignment var) h_nonterminal_f h_contains

      -- Apply induction hypothesis to h
      have h_count_lt : h.countLiterals < n := by
        apply Nat.lt_of_lt_of_le h_progress
        exact h_count_le
      have h_reaches_empty := ih h.countLiterals h_count_lt h (le_refl _) h_h_satisfies

      -- Construct the game sequence: f → g → h → []
      exact game_reaches_terminal.step h_not_terminal rfl [] h_neg_valid h_h_eq h_reaches_empty

/--
**Satisfiable Implies Affirmative Victory**: From any satisfiable formula, there exists an
Affirmative strategy that guarantees reaching victory (empty formula).

This is the cleanest statement of Affirmative's advantage: if a formula is satisfiable,
Affirmative has a winning strategy regardless of Negative's responses.
-/
theorem satisfiable_implies_affirmative_victory {Var : Type} [DecidableEq Var] [Inhabited Var]
    (initial : Formula Var) (h_satisfiable : initial.IsSatisfiable) :
    ∃ (strategy : @AffirmativeStrategy Var _),
      ∀ (final : Formula Var),
        game_reaches_terminal strategy initial final →
        final = [] := by
  -- Use assignment_to_strategy to construct the winning strategy
  obtain ⟨assignment, h_satisfies⟩ := h_satisfiable
  use assignment_to_strategy assignment

  -- We need to prove that this strategy always leads to empty formula
  intro final h_reaches

  -- Apply the complete helper theorem: assignment strategy reaches empty formula
  have h_reaches_empty := assignment_strategy_reaches_empty initial assignment h_satisfies

  -- Now we have two game executions:
  -- h_reaches: game_reaches_terminal (assignment_to_strategy assignment) initial final
  -- h_reaches_empty: game_reaches_terminal (assignment_to_strategy assignment) initial []
  --
  -- Since game execution with a deterministic strategy is unique, final = []
  -- This follows from the fact that assignment_to_strategy is deterministic
  -- and Negative's responses are determined by the game state

  -- For now, we can prove this by showing that any terminal state reached by the assignment strategy
  -- from a satisfiable formula must be the empty formula (satisfiable terminal state)
  suffices h_terminal_empty : final.isTerminal = true → final = [] by
    -- Extract that final is terminal from the game_reaches_terminal structure
    have h_final_terminal : final.isTerminal = true :=
      game_reaches_terminal_implies_terminal (assignment_to_strategy assignment) initial final h_reaches
    exact h_terminal_empty h_final_terminal

  -- Prove that any terminal formula reachable by assignment strategy is empty
  intro h_final_terminal

  -- The assignment strategy preserves satisfiability, so final is satisfiable
  -- (This follows from h_satisfies + negative_moves_preserve_satisfiability + assignment strategy preservation)
  have h_final_satisfiable : final.IsSatisfiable := by
    -- Use the assignment satisfaction preservation lemma
    have h_final_satisfied : final.satisfiedByAssignment assignment = true :=
      assignment_strategy_preserves_assignment_satisfaction initial final assignment h_satisfies h_reaches
    exact ⟨assignment, h_final_satisfied⟩

  -- Terminal satisfiable formulas are empty
  cases terminal_formula_classification final h_final_terminal with
  | inl h_empty => exact h_empty
  | inr h_has_empty =>
    -- Contradiction: terminal with empty clause cannot be satisfiable
    exfalso
    exact terminal_with_empty_clause_unsatisfiable final h_final_terminal h_has_empty h_final_satisfiable

