# SAT Game Rules

## Overview

A two-player game involving Boolean formulas in CNF (Conjunctive Normal Form). Players take turns transforming the formula until they reach a state where satisfiability can be trivially determined.

- **Affirmative player**: Wants to end up with a formula that's satisfiable
- **Negative player**: Wants to end up with a formula that's unsatisfiable

The game is designed so that, under perfect play, the Affirmative player wins iff the original formula was satisfiable, and the Negative player wins iff the original formula was unsatisfiable.

## Move Types

**Affirmative moves**: Set a variable to `true` or `false`. For example, setting `A` to `true` in the formula `(A) ∧ (¬A ∨ B)` reduces it to `(B)` — the first clause `(A)` becomes `true` and is satisfied, while in the second clause `(¬A ∨ B)`, the literal `¬A` becomes `false` and is removed, leaving just `(B)`. If the current formula is satisfiable, Affirmative can choose any variable and truth value that's part of a satisfying assignment, and the formula will still be satisfiable.

**Negative moves**: Remove a clause from the formula. If the current formula is unsatisfiable, then as long as it's not a [minimal unsatisfiable core](https://en.wikipedia.org/wiki/Unsatisfiable_core), there is some clause that can be removed that will leave the formula as unsatisfiable. In the case where it is a minimal unsatisfiable core, Negative can `pass` instead (see below).

**Negative passes**: Instead of removing a clause, Negative can `pass`, but when they do they must also offer to Affirmative the option to switch sides, so that the original Affirmative player would start playing as Negative and the original Negative player would start playing as Affirmative. If Affirmative accepts the side switch, they must immediately take a turn and remove a clause — they can't pass back on that turn (though they can pass on future turns).

The reason Negative must offer to switch sides whenever they pass is to prevent them from just always passing on every turn. Crucially though, it is only an *offer* to switch, which Affirmative can accept or decline. Affirmative would decline if they think they can still win as Affirmative, by setting variables. Affirmative would accept if they think they were losing as Affirmative (because the formula is unsatisfiable), but that the current Negative player is mistaken about whether the current formula is a minimal unsatisfiable core.

## Turn Selection

The game can be played in either of two modes — **strict alternation**, or **random turn selection**. In the **strict alternation** mode, Affirmative and Negative alternate turns, with Affirmative going first. In the **random turn selection** mode, the next player is chosen at random after each turn, possibly with a bias based on the ratio of clauses to variables in the current formula. The reason you might use a bias is because, for random SAT formulas, whether the formula is satisfiable or not is correlated with the clause-to-variable ratio — there is a [phase transition](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem#Empirical_complexity) where formulas change from almost always satisfiable to almost always unsatisfiable (around 4.27 clauses per variable for random 3-SAT, though the critical ratio varies for mixed clause lengths). You might be inclined to keep the formula near a balanced ratio, so that neither Affirmative nor Negative is unfairly advantaged.

## Winning Conditions

- **Empty formula (no clauses remaining)**: Affirmative player wins (formula is vacuously satisfiable)
- **Formula contains at least one empty clause**: Negative player wins (formula is unsatisfiable)
