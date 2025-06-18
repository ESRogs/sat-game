# SAT Game Correctness Roadmap

This document outlines our strategy for proving that "the right side wins under perfect play" in the SAT Game.

## Ultimate Goal

**Theorem**: Under perfect play by both sides, the game outcome equals the formula's satisfiability.
- If the original formula is satisfiable, Affirmative wins
- If the original formula is unsatisfiable, Negative wins

## Overall Strategy

Rather than proving game correctness directly, we break it into **pure `FormulaOp` properties** that compose cleanly:

1. **Termination**: The game always ends (no infinite play)
2. **Position Preservation**: Losing positions stay losing; winning positions can be preserved
3. **Strategy Existence**: Players with winning positions always have moves that maintain their advantage
4. **Game Composition**: Combine position preservation + strategy existence into full correctness
5. **Side-Swap Extension**: Handle the role-reversal mechanism

This modular approach keeps proofs clean and avoids mixing game semantics with formula logic.

## Phase 1: Termination ✅ COMPLETE

**Goal**: Prove that the SAT Game always terminates - no infinite play is possible.

### ✅ Completed (Prior to 2025-06-11)
- `literalCount`: Defined the termination measure (total literals across all clauses)
- `operations_eventually_terminate`: Well-foundedness of the literal count ordering
- `operation_decreases_literalCount`: Every valid operation strictly decreases literal count
- `setVariable_decreases_literalCount`: Variable assignment decreases literals
- `removeClause_decreases_literalCount`: Clause removal decreases literals

**Significance**: These properties establish that every game move brings us closer to a terminal state, ensuring the game cannot continue forever.

## Phase 2: Position Preservation ✅ COMPLETE

**Goal**: Prove that game operations preserve the fundamental position nature - losing positions remain losing.

### ✅ Completed (2025-06-11)
- `removeClause_preserves_satisfiability`: Removing clauses never turns satisfiable formulas unsatisfiable
- `setVariable_preserves_unsatisfiability`: Setting variables never turns unsatisfiable formulas satisfiable

**Significance**: These properties ensure that players cannot transform losing positions into winning ones through their moves. A player in a losing position remains in a losing position regardless of their choices.

## Phase 3: Strategy Existence ✅ COMPLETE

**Goal**: Prove that players with winning positions always have moves that preserve their advantage.

### ✅ Completed (2025-06-12)
1. **Done**: Define `Formula.isMinimalUnsatisfiableCore` ✅
2. **Done**: Prove `unsatisfiable_nonminimal_has_preserving_removeClause` ✅
3. **Done**: Prove `satisfiable_has_preserving_setVariable` ✅

**Significance**: These properties show that players in winning positions can maintain their advantage with correct play. Combined with position preservation, this ensures that initial winning positions lead to victories under perfect play.

## Phase 4: Game Composition 🔗

**Goal**: Combine position preservation and strategy existence into full game correctness.

### ⏳ Pending
- `simple_game_correctness`: Game without side-swaps has correct outcomes
- Perfect play strategy construction
- Inductive proof over game trees

**Approach**: Use position preservation to show losing players cannot escape their fate, and strategy existence to show winning players can maintain their advantage through to victory.

## Phase 5: Side-Swap Extension 🔄

**Goal**: Extend correctness to the full game with Negative's pass-and-side-swap mechanism.

### ⏳ Pending  
- Optimal side-swap decision theory
- Role-reversal dynamics analysis
- Full game correctness with side-swaps

**Challenge**: Side-swaps preserve literal count but change game state, requiring careful analysis of when they're beneficial.

## Current Implementation Status

### ✅ Complete Proofs (14)
**Phase 1 - Termination (5 proofs):**
1. `literalCount` - Termination measure definition
2. `operations_eventually_terminate` - Well-foundedness of literal count ordering
3. `operation_decreases_literalCount` - Master termination theorem
4. `setVariable_decreases_literalCount` - Variable assignment termination
5. `removeClause_decreases_literalCount` - Clause removal termination

**Phase 2 - Position Preservation (6 proofs):**
6. `removeClause_preserves_satisfiability` - Clause removal preserves satisfiable positions
7. `setVariable_preserves_unsatisfiability` - Variable assignment preserves unsatisfiable positions
8. `satisfied_clause_remains_satisfied` - Helper theorem
9. `filtered_clause_satisfaction_extends` - Helper theorem  
10. `empty_formula_satisfiable` - Basic satisfiability property
11. `assignment_extension_preserves_unrelated_literals` - Assignment extension utility

**Phase 3 - Strategy Existence (3 proofs):**
12. `Formula.isMinimalUnsatisfiableCore` - Definition of minimal unsatisfiable cores
13. `unsatisfiable_nonminimal_has_preserving_removeClause` - Negative strategy existence
14. `satisfiable_has_preserving_setVariable` - Affirmative strategy existence

### Status Summary
- ⏳ Phase 1 (Termination): COMPLETE ✅
- ⏳ Phase 2 (Position Preservation): COMPLETE ✅
- ⏳ Phase 3 (Strategy Existence): COMPLETE ✅

### 📁 Framework Ready
- Satisfiability definitions (`Assignment`, `Formula.satisfiable`, etc.)
- FormulaOp operations (`setVariable`, `removeClause`)
- Termination measure (`literalCount`)
- Assignment extension utilities

## Key Technical Challenges

### Completed Challenges ✅
1. **`setVariable_preserves_unsatisfiability`**: Required contrapositive proof with assignment extension

### Remaining Difficult Challenges
1. **Minimal unsatisfiable cores**: Characterizing when clause removal preserves unsatisfiability
2. **Strategy construction**: Building explicit winning algorithms
3. **Side-swap optimality**: Determining when role reversal benefits Negative

### Mathematical Foundations Needed
- Connection to DPLL algorithm behavior
- Resolution completeness arguments  
- SAT solver theory (minimal cores, clause redundancy)

## Proof Dependencies

```
empty_formula_satisfiable (✅)
removeClause_preserves_satisfiability (✅)
   ↓
setVariable_preserves_unsatisfiability
   ↓
satisfiable_has_preserving_setVariable
unsatisfiable_nonminimal_has_preserving_removeClause
   ↓
simple_game_correctness
   ↓
full_game_correctness_with_sideswaps
```

## Session Continuity Notes

- **Development approach**: Focus on smallest, easiest steps with complete proofs
- **Core Principle**: **Always prioritize eliminating `sorry`s over moving to new work**
- **Phase 1 completed**: All termination properties proven (prior to 2025-06-11)
- **Phase 2 completed**: All position preservation properties proven with zero sorrys (2025-06-11)
- **Phase 3 completed**: All strategy existence properties proven with zero sorrys (2025-06-12)
- **Phase 4 status**: NEARLY COMPLETE - Assignment-following strategy fully implemented (2025-06-16)
- **Infrastructure completed**: All naming conventions finalized (2025-06-12)
- **Framework status**: All definitions and basic infrastructure complete
- **Current work**: Phase 4 final proof engineering - one remaining `sorry` in complex inductive argument
- **Achievement**: Assignment-following strategy proven correct with complete 4-component roadmap
- **Current milestone**: Complete Phase 4 by implementing the final inductive termination proof

## References

- Game rules: `docs/RULES.md`
- Termination proofs: `SATGame/Termination/`
- Position preservation proofs: `SATGame/Correctness/PositionPreservation.lean`
- Strategy existence proofs: `SATGame/Correctness/StrategyExistence.lean`