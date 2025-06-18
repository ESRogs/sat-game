import SATGame.FormulaOps.FormulaExt
import SATGame.CNF.Formula

/-!
# SAT Game Examples

Demonstrations of formula transformations through game moves.

Shows how variable assignments and clause removals transform formulas,
including examples of both Affirmative and Negative victory conditions.
-/

-- Example variables for demonstrations
-- We use concrete values: p=1, q=2, r=3, s=4
def p : Nat := 1
def q : Nat := 2
def r : Nat := 3
def s : Nat := 4

/-!
## Example 1: Simple 3-SAT Formula
-/

/-- Starting formula: (p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r) -/
def example1Start : Formula Nat := [
  [Literal.pos p, Literal.pos q],           -- p ∨ q
  [Literal.neg p, Literal.pos r],           -- ¬p ∨ r
  [Literal.neg q, Literal.neg r]            -- ¬q ∨ ¬r
]

/-- After Affirmative sets p := true
    Formula becomes: (r) ∧ (¬q ∨ ¬r)
    - First clause (p ∨ q) is satisfied and removed
    - Second clause (¬p ∨ r) has ¬p removed, leaving just r
    - Third clause unchanged
-/
def example1AfterPTrue : Formula Nat :=
  example1Start.setVariable p true

-- Expected: [[Literal.pos r], [Literal.neg q, Literal.neg r]]

/-- After Negative removes the first clause (r)
    Formula becomes: (¬q ∨ ¬r)
-/
def example1AfterRemoveR : Formula Nat :=
  example1AfterPTrue.removeClause 0

-- Expected: [[Literal.neg q, Literal.neg r]]

/-- After Affirmative sets q := false
    Formula becomes: [] (empty formula)
    - The clause (¬q ∨ ¬r) has ¬q become true, so the whole clause is satisfied and removed
-/
def example1AfterQFalse : Formula Nat :=
  example1AfterRemoveR.setVariable q false

-- Expected: [] (empty formula - Affirmative wins!)

/-!
## Example 2: Unsatisfiable Formula Leading to Empty Clause
-/

/-- Starting formula: (p) ∧ (¬p) - clearly unsatisfiable -/
def example2Start : Formula Nat := [
  [Literal.pos p],                          -- p
  [Literal.neg p]                           -- ¬p
]

/-- After Affirmative sets p := true
    Formula becomes: ([]) - empty clause, Negative wins!
    - First clause (p) is satisfied and removed
    - Second clause (¬p) has ¬p become false, leaving empty clause
-/
def example2AfterPTrue : Formula Nat :=
  example2Start.setVariable p true

-- Expected: [[]] (contains empty clause - Negative wins!)

/-!
## Example 3: Complex Formula with Multiple Variables
-/

/-- Starting formula: (p ∨ q ∨ r) ∧ (¬p ∨ s) ∧ (¬q ∨ ¬s) ∧ (¬r ∨ ¬s) -/
def example3Start : Formula Nat := [
  [Literal.pos p, Literal.pos q, Literal.pos r],    -- p ∨ q ∨ r
  [Literal.neg p, Literal.pos s],                    -- ¬p ∨ s
  [Literal.neg q, Literal.neg s],                    -- ¬q ∨ ¬s
  [Literal.neg r, Literal.neg s]                     -- ¬r ∨ ¬s
]

/-- After Affirmative sets s := true
    Formula becomes: (p ∨ q ∨ r) ∧ (¬q) ∧ (¬r)
    - Second clause (¬p ∨ s) is satisfied by s and removed
    - Third clause (¬q ∨ ¬s) has ¬s removed, leaving ¬q
    - Fourth clause (¬r ∨ ¬s) has ¬s removed, leaving ¬r
-/
def example3AfterSTrue : Formula Nat :=
  example3Start.setVariable s true

-- Expected: [[Literal.pos p, Literal.pos q, Literal.pos r], [Literal.neg q], [Literal.neg r]]

/-- After Affirmative sets q := false
    Formula becomes: (p ∨ r) ∧ (¬r)
    - First clause has q removed, leaving p ∨ r
    - Second clause (¬q) is satisfied and removed
    - Third clause (¬r) unchanged
-/
def example3AfterQFalse : Formula Nat :=
  example3AfterSTrue.setVariable q false

-- Expected: [[Literal.pos p, Literal.pos r], [Literal.neg r]]

/-- After Affirmative sets r := true
    Formula becomes: ([])
    - First clause (p ∨ r) is satisfied by r and removed
    - Second clause (¬r) has ¬r become false, leaving empty clause
-/
def example3AfterRTrue : Formula Nat :=
  example3AfterQFalse.setVariable r true

-- Expected: [[]] (empty clause - Negative wins!)

/-!
## Example 4: Strategic Clause Removal
-/

/-- Starting formula: (p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ r) -/
def example4Start : Formula Nat := [
  [Literal.pos p, Literal.pos q],           -- p ∨ q
  [Literal.pos p, Literal.neg q],           -- p ∨ ¬q
  [Literal.neg p, Literal.pos r]            -- ¬p ∨ r
]

/-- Strategic move: Negative removes the third clause
    This prevents Affirmative from having a backup if p is set false
-/
def example4AfterRemoveThird : Formula Nat :=
  example4Start.removeClause 2

-- Expected: [[Literal.pos p, Literal.pos q], [Literal.pos p, Literal.neg q]]

/-- After Affirmative sets p := false
    Formula becomes: (q) ∧ (¬q)
    - Both clauses have p removed
-/
def example4AfterPFalse : Formula Nat :=
  example4AfterRemoveThird.setVariable p false

-- Expected: [[Literal.pos q], [Literal.neg q]]

/-!
## Example 5: Negative Pass Move and Side-Swap Strategy
-/

/-- Starting formula: (p ∨ q) ∧ (¬p ∨ ¬q) ∧ (r)
    This formula is satisfiable: set p=true, q=false, r=true -/
def example5Start : Formula Nat := [
  [Literal.pos p, Literal.pos q],           -- p ∨ q
  [Literal.neg p, Literal.neg q],           -- ¬p ∨ ¬q
  [Literal.pos r]                           -- r
]

/-- Strategic move: Negative passes instead of making a move
    In the actual game, this would trigger a side-swap offer where:
    - Affirmative can accept (roles reverse) or decline
    - If declined, Negative must make a move

    For demonstration, we show what happens if Affirmative declines
    and Negative removes the third clause (r) -/
def example5AfterNegativeRemovesR : Formula Nat :=
  example5Start.removeClause 2

-- Expected: [[Literal.pos p, Literal.pos q], [Literal.neg p, Literal.neg q]]

/-- Now Affirmative faces a difficult choice:
    - If p=true, then first clause satisfied, but second needs q=false
    - If p=false, then second clause satisfied, but first needs q=true
    Both paths lead to satisfaction, showing why Negative tried to pass -/
def example5AfterPTrue : Formula Nat :=
  example5AfterNegativeRemovesR.setVariable p true

-- Expected: [[Literal.neg q]] (Affirmative can win by setting q=false)

/-!
## Example 6: Side-Swap Acceptance Strategy
-/

/-- Starting formula: (p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r) ∧ (s ∨ ¬s)
    Note: Last clause (s ∨ ¬s) is a tautology, making formula satisfiable -/
def example6Start : Formula Nat := [
  [Literal.pos p, Literal.pos q],           -- p ∨ q
  [Literal.neg p, Literal.pos r],           -- ¬p ∨ r
  [Literal.neg q, Literal.neg r],           -- ¬q ∨ ¬r
  [Literal.pos s, Literal.neg s]            -- s ∨ ¬s (tautology)
]

/-- If Negative passes and Affirmative accepts the side-swap,
    then Affirmative (now playing Negative role) might remove the tautology
    to make the game more challenging for the original Negative player -/
def example6AfterSideswapRemoveTautology : Formula Nat :=
  example6Start.removeClause 3

-- Expected: [[Literal.pos p, Literal.pos q], [Literal.neg p, Literal.pos r], [Literal.neg q, Literal.neg r]]
-- This creates the classic 3-SAT example from Example 1, demonstrating how side-swaps transform game dynamics

/-!
## Verification Examples
-/

/-- Verify that Example 1 ends in Affirmative victory (empty formula) -/
example : example1AfterQFalse = [] := by rfl

/-- Verify that Example 2 ends in Negative victory (empty clause) -/
example : example2AfterPTrue.hasEmptyClause = true := by rfl

/-- Verify that Example 3 ends in Negative victory (empty clause) -/
example : example3AfterRTrue.hasEmptyClause = true := by rfl

/-- Verify that Example 5 shows strategic complexity -/
example : example5AfterPTrue = [[Literal.neg q]] := by rfl

/-- Verify that Example 6 side-swap creates the familiar pattern -/
example : example6AfterSideswapRemoveTautology = example1Start := by rfl

/-!
## Termination Demonstration
-/

/-- Eventually reaching terminal state (empty formula or empty clause) -/
example : example1AfterQFalse.isTerminal = true := by rfl
example : example2AfterPTrue.isTerminal = true := by rfl

/-!
## Helper Functions for Analysis
-/

/-- Count total number of literals in a formula -/
def totalLiterals (formula : Formula Nat) : Nat := formula.countLiterals

/-- Check if formula is in terminal state -/
def isGameOver (formula : Formula Nat) : Bool := formula.isTerminal

/-- Demonstrate literal count progression in Example 1 -/
def example1LiteralProgression : List Nat := [
  example1Start.countLiterals,
  example1AfterPTrue.countLiterals,
  example1AfterRemoveR.countLiterals,
  example1AfterQFalse.countLiterals
]

-- Expected: [6, 3, 2, 0] - strictly decreasing sequence
