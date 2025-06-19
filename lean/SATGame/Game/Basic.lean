import SATGame.CNF.Satisfiability
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.ValidSequences
import SATGame.FormulaOps.Termination.Nonterminal
import SATGame.FormulaOps.Termination.SetVariable
import SATGame.FormulaOps.Termination.RemoveClause

/-!
# SAT Game Basic Concepts

This module defines the core concepts for the two-player SAT Game built on top of
the mathematical formula operations framework.

## Players and Game Rules

1. **Affirmative Player**: Tries to satisfy the formula using `setVariable` operations
2. **Negative Player**: Tries to make the formula unsatisfiable using `removeClause` operations
3. **Terminal States**: Game ends when no more operations can be applied (`isTerminal = true`)
4. **Winning Conditions**:
   - Affirmative wins if terminal formula is empty (satisfied)
   - Negative wins if terminal formula has empty clause (unsatisfiable)

## Game Structures

- `AffMoveRound`: One cycle of play (Affirmative move + Negative response)
- Game proceeds through alternating rounds until reaching a terminal state
-/

/-!
## Player Definitions
-/

/-- The two players in the SAT Game -/
inductive Player where
  | Affirmative : Player  -- Tries to satisfy (uses setVariable)
  | Negative : Player     -- Tries to unsatisfy (uses removeClause)

/-!
## Winning Conditions
-/

/-- Affirmative wins when the terminal formula is empty (all clauses satisfied) -/
def Affirmative_wins {Var : Type} (formula : Formula Var) : Prop :=
  formula.isTerminal ∧ formula = []

/-- Negative wins when the terminal formula contains an empty clause (unsatisfiable) -/
def Negative_wins {Var : Type} (formula : Formula Var) : Prop :=
  formula.isTerminal ∧ formula.hasEmptyClause

/-- Every terminal formula has a determined winner -/
theorem terminal_formula_has_winner {Var : Type} (formula : Formula Var)
    (h_terminal : formula.isTerminal = true) :
    Affirmative_wins formula ∨ Negative_wins formula := by
  -- Use the mathematical classification theorem
  cases terminal_formula_classification formula h_terminal with
  | inl h_empty =>
    -- formula = [] → Affirmative wins
    left
    constructor
    · exact h_terminal
    · exact h_empty
  | inr h_has_empty =>
    -- formula.hasEmptyClause → Negative wins
    right
    constructor
    · exact h_terminal
    · exact h_has_empty

/-!
## Game Round Structures
-/

/--
An AffMoveRound represents one cycle of play from Affirmative's perspective:
Affirmative makes one move, then Negative makes zero or more response moves.
-/
structure AffMoveRound (Var : Type) where
  aff_move : FormulaOp Var           -- Exactly one move by Affirmative
  neg_response : List (FormulaOp Var) -- Zero or more moves by Negative

/-- Apply an AffMoveRound to a formula -/
def apply_aff_move_round {Var : Type} [DecidableEq Var] (formula : Formula Var) (round : AffMoveRound Var) : Formula Var :=
  let after_aff := formula.applyOp round.aff_move
  round.neg_response.foldl Formula.applyOp after_aff

/-!
## Helper Functions for Multi-Round Analysis
-/

/-- Apply one round of the Affirmative strategy with Negative's response -/
def apply_one_aff_round {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (aff_strategy : Formula Var → FormulaOp Var)
    (neg_behavior : Formula Var → List (FormulaOp Var)) : Formula Var :=
  let aff_move := aff_strategy formula
  let after_aff := formula.applyOp aff_move
  let neg_response := neg_behavior after_aff
  neg_response.foldl Formula.applyOp after_aff

/-- Iterate AffMoveRounds for a given number of rounds -/
def iterate_aff_move_rounds {Var : Type} [DecidableEq Var]
    (initial : Formula Var)
    (aff_strategy : Formula Var → FormulaOp Var)
    (neg_behavior : Formula Var → List (FormulaOp Var))
    (num_rounds : Nat) : Formula Var :=
  match num_rounds with
  | 0 => initial
  | n + 1 =>
    let after_n_rounds := iterate_aff_move_rounds initial aff_strategy neg_behavior n
    if after_n_rounds.isTerminal then
      after_n_rounds
    else
      apply_one_aff_round after_n_rounds aff_strategy neg_behavior

/-!
## Affirmative Strategies
-/

/--
**Affirmative Strategy**: A valid strategy that maps nonterminal formulas to applicable SetVariable operations.

This captures the essence of what Affirmative needs: for any nonterminal formula,
the ability to choose a variable that exists in the formula and assign it a value.
-/
structure AffirmativeStrategy {Var : Type} [DecidableEq Var] where
  strategy : (f : Formula Var) → f.isTerminal = false →
    { op : FormulaOp Var // ∃ (var : Var) (val : Bool), op = FormulaOp.SetVariable var val ∧ op.IsApplicable f }

/-!
## Assignment-Following Strategy
-/

/--
**Assignment-Following Strategy**: A strategy where Affirmative sets variables according to a given satisfying assignment.

For nonterminal formulas, chooses a variable and sets it to the assignment's value.
For terminal formulas, makes a default move (though this shouldn't happen in normal play).
-/
noncomputable def assignment_following_strategy {Var : Type} [DecidableEq Var] [Inhabited Var]
    (assignment : Assignment Var) : Formula Var → FormulaOp Var := fun formula =>
  if h : formula.isTerminal then
    FormulaOp.SetVariable default false
  else
    -- Since formula.isTerminal = false, we know formula.isNonterminal = true
    have h_nonterminal : formula.isNonterminal = true := by
      unfold Formula.isNonterminal
      simp [h]
    let var := Classical.choose (nonterminal_contains_variable formula h_nonterminal)
    FormulaOp.SetVariable var (assignment var)

/-!
## Valid Game Rounds and Sequences
-/

/--
**Valid Affirmative Move Round**: A round where both players make valid, applicable moves.
- Affirmative uses SetVariable on a variable that exists in the formula
- Negative uses a valid clause removal sequence
-/
structure ValidAffMoveRound {Var : Type} [DecidableEq Var] (formula : Formula Var) where
  round : AffMoveRound Var
  formula_not_terminal : formula.isTerminal = false
  aff_is_applicable : round.aff_move.IsApplicable formula
  aff_is_set_var : ∃ (var : Var) (val : Bool), round.aff_move = FormulaOp.SetVariable var val
  neg_is_valid_removal : valid_clause_removal_sequence (formula.applyOp round.aff_move) round.neg_response

/--
**Valid Assignment Game Sequence**: Game sequence where Affirmative follows assignment strategy
using valid rounds.
-/
inductive valid_assignment_game_sequence {Var : Type} [DecidableEq Var] [Inhabited Var]
    (assignment : Assignment Var) :
    Formula Var → Formula Var → Prop where
  | nil (f : Formula Var) :
      valid_assignment_game_sequence assignment f f
  | cons {f g h : Formula Var}
      (round : ValidAffMoveRound f)
      (h_aff_follows : round.round.aff_move = assignment_following_strategy assignment f)
      (h_step : g = apply_aff_move_round f round.round)
      (h_rest : valid_assignment_game_sequence assignment g h) :
      valid_assignment_game_sequence assignment f h

/--
**Affirmative Victory Reachability**: A formula reaches empty (Affirmative victory)
through a valid assignment game sequence.
-/
def affirmative_can_reach_victory {Var : Type} [DecidableEq Var] [Inhabited Var]
    (initial : Formula Var)
    (assignment : Assignment Var) : Prop :=
  valid_assignment_game_sequence assignment initial []

/--
**Game Termination**: The game with assignment strategy reaches a terminal state.
-/
def game_eventually_terminates {Var : Type} [DecidableEq Var] [Inhabited Var]
    (initial : Formula Var)
    (assignment : Assignment Var) : Prop :=
  ∃ (final : Formula Var),
    final.isTerminal = true ∧
    valid_assignment_game_sequence assignment initial final


/-!
## Game Execution with Strategies
-/

/--
**Game Reaches Terminal**: Predicate for game execution reaching a terminal state using an Affirmative strategy.

This captures the actual game dynamics: Affirmative makes moves according to their strategy,
Negative responds with valid clause removal sequences, and the game continues until terminal.
-/
inductive game_reaches_terminal {Var : Type} [DecidableEq Var]
    (strategy : @AffirmativeStrategy Var _) : Formula Var → Formula Var → Prop where
  | terminal (f : Formula Var) (h : f.isTerminal = true) :
      game_reaches_terminal strategy f f
  | step {f g h final : Formula Var}
      (h_not_terminal : f.isTerminal = false)
      (h_aff_move : g = f.applyOp (strategy.strategy f h_not_terminal).val)
      (neg_moves : List (FormulaOp Var))
      (h_neg_valid : valid_clause_removal_sequence g neg_moves)
      (h_neg_apply : h = neg_moves.foldl Formula.applyOp g)
      (h_rest : game_reaches_terminal strategy h final) :
      game_reaches_terminal strategy f final

/--
**Assignment to Strategy**: Convert a satisfying assignment to an AffirmativeStrategy.

Given an assignment, we create a strategy that sets each variable according to the assignment.
This is noncomputable because it uses Classical.choose to extract variables from formulas.
-/
noncomputable def assignment_to_strategy {Var : Type} [DecidableEq Var] [Inhabited Var]
    (assignment : Assignment Var) : @AffirmativeStrategy Var _ :=
  { strategy := fun f h_not_terminal =>
      -- Since f is not terminal, it's nonterminal and contains variables
      have h_nonterminal : f.isNonterminal = true := by
        unfold Formula.isNonterminal
        simp [h_not_terminal]
      let var := Classical.choose (nonterminal_contains_variable f h_nonterminal)
      have h_contains := Classical.choose_spec (nonterminal_contains_variable f h_nonterminal)
      ⟨FormulaOp.SetVariable var (assignment var),
       ⟨var, assignment var, rfl, h_contains⟩⟩ }
