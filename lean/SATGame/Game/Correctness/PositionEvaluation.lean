import SATGame.Game.Basic
import SATGame.FormulaOps.SatisfiabilityPreservation

/-!
# Position Evaluation

This module provides game-theoretic interpretations of the mathematical preservation
properties proven in FormulaOps.SatisfiabilityPreservation.

## Key Game Principle: Losing Positions Remain Losing

The mathematical preservation theorems ensure that:
- **Affirmative** cannot turn losing positions (unsatisfiable formulas) into winning positions
- **Negative** cannot turn losing positions (satisfiable formulas) into winning positions

This is the foundation of fair play in the SAT Game.

## Player-Specific Interpretations

### Affirmative's Constraints
- Cannot make unsatisfiable formulas satisfiable through `setVariable` moves
- Valid sequences of variable assignments preserve unsatisfiability
- Must work within the constraint that losing positions stay losing

### Negative's Constraints
- Cannot make satisfiable formulas unsatisfiable through `removeClause` moves
- Valid sequences of clause removals preserve satisfiability
- Must work within the constraint that losing positions stay losing

## Game Fairness

These preservation properties ensure the SAT Game is fair:
- Neither player can "cheat" by transforming a losing position into a winning one
- The winner is determined by the initial formula's satisfiability, not by invalid moves
- All valid play respects the fundamental logical structure of the formula
-/

/-!
## Game-Theoretic Interpretations of Mathematical Preservation
-/

/--
Affirmative cannot transform losing positions (unsatisfiable formulas) into winning positions.
This is the game interpretation of `setVariable_preserves_unsatisfiability`.
-/
theorem affirmative_cannot_escape_losing_position {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool)
    (h_losing : ¬formula.IsSatisfiable) :
    ¬(formula.setVariable var value).IsSatisfiable :=
  setVariable_preserves_unsatisfiability formula var value h_losing

/--
Negative cannot transform losing positions (satisfiable formulas) into winning positions.
This is the game interpretation of `removeClause_preserves_satisfiability`.
-/
theorem negative_cannot_escape_losing_position {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (index : Nat)
    (h_losing : formula.IsSatisfiable) :
    (formula.removeClause index).IsSatisfiable :=
  removeClause_preserves_satisfiability formula index h_losing

/-!
## Sequence-Based Game Fairness
-/

/--
Affirmative cannot escape losing positions through any valid sequence of moves.
Game interpretation of `valid_variable_assignment_sequence_preserves_unsatisfiability`.
-/
theorem affirmative_sequence_cannot_escape_losing {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_losing : ¬formula.IsSatisfiable)
    {assignments : List (FormulaOp Var)}
    (valid_sequence : valid_variable_assignment_sequence formula assignments) :
    ¬(assignments.foldl Formula.applyOp formula).IsSatisfiable :=
  valid_variable_assignment_sequence_preserves_unsatisfiability formula h_losing valid_sequence

/--
Negative cannot escape losing positions through any valid sequence of moves.
Game interpretation of `valid_clause_removal_sequence_preserves_satisfiability`.
-/
theorem negative_sequence_cannot_escape_losing {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_losing : formula.IsSatisfiable)
    {removals : List (FormulaOp Var)}
    (valid_sequence : valid_clause_removal_sequence formula removals) :
    (removals.foldl Formula.applyOp formula).IsSatisfiable :=
  valid_clause_removal_sequence_preserves_satisfiability formula h_losing valid_sequence

/-!
## Game Outcome Determinism
-/

/--
**Strategic Operation Preservation**: The preservation properties that actually matter for game strategy.

Rather than claiming that game sequences preserve satisfiability in both directions (which is false),
this theorem establishes the preservation properties that enable strategic play:

1. **Negative can't destroy satisfiability**: If a formula is satisfiable when Negative gets to move,
   Negative's removeClause operations preserve satisfiability (they can't force unsatisfiability).

2. **Affirmative can't create satisfiability**: If a formula is unsatisfiable when Affirmative gets to move,
   Affirmative's setVariable operations preserve unsatisfiability (they can't force satisfiability).

These are the key properties that prevent players from "accidentally" helping their opponent.
-/
theorem strategic_operation_preservation {Var : Type} [DecidableEq Var] :
    -- Negative can't destroy satisfiability with removeClause
    (∀ (formula : Formula Var) (neg_moves : List (FormulaOp Var)),
      formula.IsSatisfiable →
      valid_clause_removal_sequence formula neg_moves →
      (neg_moves.foldl Formula.applyOp formula).IsSatisfiable) ∧
    -- Affirmative can't create satisfiability with setVariable
    (∀ (formula : Formula Var) (aff_moves : List (FormulaOp Var)),
      ¬formula.IsSatisfiable →
      valid_variable_assignment_sequence formula aff_moves →
      ¬(aff_moves.foldl Formula.applyOp formula).IsSatisfiable) := by
  constructor
  · intro formula neg_moves h_satisfiable h_neg_valid
    -- Use our preservation theorem directly
    exact valid_clause_removal_sequence_preserves_satisfiability formula h_satisfiable h_neg_valid
  · intro formula aff_moves h_unsatisfiable h_aff_valid
    -- Use our preservation theorem directly
    exact valid_variable_assignment_sequence_preserves_unsatisfiability formula h_unsatisfiable h_aff_valid
