# SAT Game

A two-player strategic game for Boolean satisfiability problems.

## Overview

Two players take turns transforming a Boolean formula in CNF (Conjunctive Normal Form) until it is trivially evaluable as either satisfiable (due to having no clauses remaining) or unsatisfiable (due to having at least one empty clause remaining):

- **Affirmative** (wants satisfiable outcome): Sets variables to true/false
- **Negative** (wants unsatisfiable outcome): Removes clauses

## Rules

See [docs/RULES.md](./docs/RULES.md) for complete game rules.

## Motivation

Inspired by [AlphaZero](https://en.wikipedia.org/wiki/AlphaZero) and [Logical Induction](https://arxiv.org/abs/1609.03543), this game was designed to give neural networks a new way to learn to assign probabilities to logical statements.

Consider an arbitrary chess position and the statement, "This position is winning for white, assuming perfect play." For a given chess position, that statement has a well-defined answer, but, in the general case, it's totally intractable to assess its truth value, since that would require analyzing the complete game tree starting from that position. On the other hand, if you wanted to make a bet as to whether the position was winning, it might be a good idea to consult AlphaZero (or another modern chess engine) to see what it thinks of the position.

Notably, AlphaZero hasn't been trained to directly answer the question of whether a position is winning assuming perfect play. It's just been trained to play the game and win. We would conjecture though that AlphaZero's assessment of the strength of a chess position is generally correlated with that position's winningness assuming perfect play.

Similarly, we conjecture that neural networks could productively be used to assign probabilities to a broader class of logical statements (besides just statements about chess or go positions) by training them to play games that explicitly work with logical statements. We have designed this game to work with Boolean formulas, with the hope that neural networks trained to play it could be used to assess whether a given formula is likely to be satisfiable. These assessments could then be used to help guide SAT solvers.

Generally speaking, modern state-of-the-art SAT solvers work by trying to assign variables and then backtracking if they run into a conflict. They use relatively simple, but cheap-to-evaluate heuristics to guide their decisions about what variables to set.

In contrast, we imagine that neural networks trained to play this game might learn more sophisticated heuristics for choosing which variables to set. While evaluating these heuristics would be computationally expensive — requiring a forward pass through a neural network rather than the simple calculations SAT solvers typically use — smarter variable selection could dramatically reduce the search space. The holy grail would be exploring so many fewer variable assignments that we use less computation overall, despite the higher cost per decision.

By way of analogy, in 2018 the AlphaZero chess engine analyzed only [60,000 positions per second](https://deepmind.google/discover/blog/alphazero-shedding-new-light-on-chess-shogi-and-go/) compared to Stockfish's 60 million, yet achieved superior performance through more intelligent position evaluation. And for SAT solvers specifically, there has been some progress using heuristics learned by neural networks to improve solver performance. (See, for example, [NeuroCore](https://arxiv.org/abs/1903.04671), which helped SAT solvers solve 6-20% more problems by using neural networks to guide variable selection.)

At this point we don't know if neural networks trained to play our game will be able to improve SAT solver performance. But we are interested to find out.

## License

MIT
