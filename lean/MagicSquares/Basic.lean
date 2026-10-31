import Mathlib.Tactic

/-!
# 3×3 magic squares of squares: definitions and the Lucas form

A `MagicSquareOfSquares` is a 3×3 array of positive integers `r i j` whose squares form a
magic square (all rows, columns and both diagonals have equal sums) with nine pairwise
distinct entries.  No existence is claimed: the famous open problem asks whether any
exists.  Everything proved here is a *necessary condition* on a hypothetical example.
-/

namespace MagicSquares

/-- A 3×3 integer array is magic when all rows, all columns and both diagonals have one
common sum. -/
def IsMagic (M : Fin 3 → Fin 3 → ℤ) : Prop :=
  ∃ S : ℤ, (∀ i, M i 0 + M i 1 + M i 2 = S) ∧ (∀ j, M 0 j + M 1 j + M 2 j = S) ∧
    M 0 0 + M 1 1 + M 2 2 = S ∧ M 0 2 + M 1 1 + M 2 0 = S

/-- A 3×3 magic square of nine pairwise distinct positive integer squares, recorded through
its positive square roots `r i j`. -/
structure MagicSquareOfSquares where
  /-- the (positive) square roots of the nine entries -/
  r : Fin 3 → Fin 3 → ℤ
  pos : ∀ i j, 0 < r i j
  magic : IsMagic fun i j => r i j ^ 2
  distinct : Function.Injective fun p : Fin 3 × Fin 3 => r p.1 p.2 ^ 2

namespace MagicSquareOfSquares

variable (M : MagicSquareOfSquares)

/-- The center root `e`; the center entry is `e ^ 2`. -/
def e : ℤ := M.r 1 1

/-- The corner offset `a`: the top-left entry is `e ^ 2 + a`. -/
def a : ℤ := M.r 0 0 ^ 2 - M.e ^ 2

/-- The corner offset `b`: the top-right entry is `e ^ 2 + b`. -/
def b : ℤ := M.r 0 2 ^ 2 - M.e ^ 2

/-- **Lucas form.**  Every entry is `e^2` plus a signed combination of the offsets `a, b`:
```
e²+a     e²-a-b   e²+b
e²-a+b   e²       e²+a-b
e²-b     e²+a+b   e²-a
```
-/
theorem lucas :
    M.r 0 1 ^ 2 = M.e ^ 2 - M.a - M.b ∧ M.r 1 0 ^ 2 = M.e ^ 2 - M.a + M.b ∧
    M.r 1 2 ^ 2 = M.e ^ 2 + M.a - M.b ∧ M.r 2 0 ^ 2 = M.e ^ 2 - M.b ∧
    M.r 2 1 ^ 2 = M.e ^ 2 + M.a + M.b ∧ M.r 2 2 ^ 2 = M.e ^ 2 - M.a := by
  obtain ⟨S, hrow, hcol, hd1, hd2⟩ := M.magic
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  simp only at r0 r1 r2 c0 c1 c2 hd1 hd2
  simp only [a, b, e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Distinct cells have distinct entries. -/
theorem sq_ne {i j i' j' : Fin 3} (h : (i, j) ≠ (i', j')) : M.r i j ^ 2 ≠ M.r i' j' ^ 2 :=
  fun hh => h (M.distinct (a₁ := (i, j)) (a₂ := (i', j')) hh)

end MagicSquareOfSquares

end MagicSquares
