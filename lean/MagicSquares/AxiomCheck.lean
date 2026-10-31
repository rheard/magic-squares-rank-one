import MagicSquares.RankOne

/-!
# Axiom check

Each `#guard_msgs` below fails the build unless `#print axioms` reports exactly Lean's three standard
axioms `propext`, `Classical.choice` and `Quot.sound`. So no main result uses `sorry` (which would
appear as `sorryAx`) or any added axiom. The two cited theorems enter only as hypotheses.
-/

/--
info: 'MagicSquares.RankOne.xc_add_ne_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.RankOne.xc_add_ne_two_mul

/--
info: 'MagicSquares.RankOne.ThreeProgressions.two_le_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.RankOne.ThreeProgressions.two_le_finrank

/--
info: 'MagicSquares.MagicSquareOfSquares.two_le_finrank_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.MagicSquareOfSquares.two_le_finrank_b

/--
info: 'MagicSquares.MagicSquareOfSquares.two_le_finrank_a' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.MagicSquareOfSquares.two_le_finrank_a

/--
info: 'MagicSquares.MagicSquareOfSquares.rank_two_of_antidiagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.MagicSquareOfSquares.rank_two_of_antidiagonal

/--
info: 'MagicSquares.MagicSquareOfSquares.rank_two_of_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MagicSquares.MagicSquareOfSquares.rank_two_of_diagonal
