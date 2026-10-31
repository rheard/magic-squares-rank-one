# The rank-one result in plain language

This explains what [the paper](paper/rank1-exclusion.pdf) proves, why it matters, and how it was found. It
assumes only school algebra; the few technical words are explained as they come up.

## The problem

Can you fill a 3×3 grid with nine **different perfect squares** (1, 4, 9, 16, …) so that every row, every column
and both diagonals add up to the same total? Nobody knows.
- The question was popularized in 1984 (LaBar) and by Martin Gardner, who offered a prize.
- Computer searches have checked enormous ranges and found nothing.
- The famous near-misses: Bremner's magic square has seven squares out of nine, and Sallows's square has
  nine squares but one diagonal with the wrong total.

## Step 1: magic squares are built from "three numbers in a row"

Every 3×3 magic square has a center number E and two "offsets" a and b. The nine entries are E, E ± a, E ± b,
E ± (a + b) and E ± (a − b), arranged so all the lines balance.

Inside any magic square there are evenly spaced triples, called **arithmetic progressions**: three numbers with the
same gap, like 1, 25, 49 (gaps of 24).
- The anti-diagonal is (E − b, E, E + b).
- The two "broken" diagonals parallel to it, which wrap around the edges, are also triples with gap b.
- The middles of those three triples are E − a, E and E + a, which are themselves evenly spaced.

So in a magic square of squares you get **three triples of squares, all with the same gap b, whose middles are
evenly spaced**. The same happens in the other diagonal direction, with gap a.

## Step 2: three squares in a row are points on a curve

This connection goes back to Fermat and Euler. Three squares with a common gap n match up with a point on the
curve

  y² = x³ − n²x,

called a **congruent number curve**. The same curve answers the ancient question of which numbers can be the area
of a right triangle with rational sides.

Example: 1, 25, 49 has gap 24 = 6 × 2². Shrinking everything by 2² gives 1/4, 25/4, 49/4, with gap 6. The middle
one, 25/4, is the x-coordinate of a point on y² = x³ − 36x.

So a magic square of squares gives **three points on one such curve whose x-coordinates are evenly spaced**.
Robertson observed this in 1996.

## Step 3: points on the curve can be added, and "rank" counts the starting points

Points on these curves can be "added" by a classical geometric rule: draw a line through two points and see where
it hits the curve again. This turns the curve's rational points into a **group**.

The **rank** says how many independent starting points you need to reach every point by adding.
- **Rank 0:** only a few special points exist.
- **Rank 1:** every point is a multiple of one starting point H: H, 2H, 3H, …, or a negative of one.
- **Rank 2 or more:** you need two or more independent starting points.

For the gap-6 curve (the 1, 25, 49 example), the rank is 1.

## Step 4: every new multiple brings a brand-new prime

Write the x-coordinate of each multiple of H as a fraction. Its denominator keeps picking up primes **that never
appeared before**. These are the actual numbers on the gap-6 curve, computed with PARI/GP:

| multiple | x-coordinate | new primes in the denominator |
|---|---|---|
| H | 5² / 2² | 2 |
| 2H | 1201² / 140² | 5, 7 |
| 3H | 7776485² / 2639802² | 3, 11, 23, 37, 47 |
| 4H | (13 digits)² / (12 digits)² | 1151, 1201, 1249 |
| 5H | (20 digits)² / (19 digits)² | 13, 17, 19, 73, 97, 139, 239, 719, 3121 |

There's a familiar cousin of this in the **Fibonacci numbers**: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233,
377, …. Every Fibonacci number after the 12th has a prime factor that never divided an earlier one: 233 is new,
377 = 13 × 29 brings 29, and so on. That's Carmichael's theorem.

For our curves, the same fact was proved by Voutier and Yabuta in 2012, with a gap in one lemma fixed by Verzobio
in 2021. From the third multiple on, **every multiple has a brand-new prime** in its denominator. Mathematicians
call it a **primitive divisor**.

## Step 5: the punchline

Suppose the three evenly spaced points from a magic square all came from one starting point, say 2H, 3H and 5H.
"Evenly spaced" means

  x(first) + x(third) = 2 × x(middle).

Take the multiple with the largest number; here that's 5H. Its denominator contains a prime the other two
denominators don't have. A fraction with that prime in its denominator can't be cancelled by fractions without
it, so the equation can't balance. **Contradiction.**

So the three points can't all be multiples of one point. The curve, and in fact the group those three points
generate, must have **rank at least 2**. The same argument applies to the other diagonal direction.

## What this does and doesn't show

**It does not solve the problem.** A magic square of squares could still exist on curves of rank 2 or more.

**What it does show:**
- **A proven restriction on any solution.** The gap of each diagonal, reduced to its squarefree part n, must give
  a curve of rank at least 2.
  - Such n are rare: by Smith's 2017 theorem they make up 0% of all numbers.
  - The smallest are 34, 41, 65, 137, 138 and 145.
  - Example: no magic square of squares has a diagonal with gap 6 × k², so 1, 25, 49 can never be a diagonal.
  - **Near misses usually share it, but not always.** Two triples of squares already give two of the three
    points, and those two can be multiples of one point. Here is a magic square with six squares on the
    gap-6 curve, which has rank 1:

    ```
    2762302     70²       1249²
      490²     1201²    2644702
     1151²    2879902     350²
    ```

    Two of its triples, 1151², 1201², 1249² and 70² × (1, 25, 49), give the points 2H and H. So the proof
    really needs all three triples. Still, in every near miss we checked, the two points are independent:
    Bremner's square and 2,320 six-square configurations found by computer. An exact computation proves it,
    with no rounding. So the restriction alone doesn't tell magic squares apart from these near misses.
    What's new is the proof that every magic square of squares must satisfy it (Remark 5.3 of the paper).
- **It completes something experts started.** Bremner, Silverman and Tzanakis (2000), motivated by this exact
  problem, proved the version for **whole-number** points. Real magic squares of squares never produce whole-number
  points: their gaps are always divisible by 8, so after shrinking the points are fractions. Our version handles
  fractions, which is what the magic square problem actually needs. The proof is also completely different and
  much shorter, because it uses the 2012 theorem, which they didn't have.
- **It pins down where the remaining difficulty lies.** In rank 2 or more, the same "new prime" idea would need a
  bound on how many primes two *unrelated* points' denominators can share. That is a famous open problem (Vojta's
  conjecture), and it is exactly the barrier.
- **It's short and machine-checked.** Given the cited theorem, the proof is half a page, and a computer has
  checked every step (next section).

## The computer-checked proof

[Lean](https://lean-lang.org) is a *proof assistant*: you write a proof in a precise language, and a small
trusted core checks every step, down to the axioms of mathematics. It doesn't accept "clearly" or "similarly".
The file [`lean/MagicSquares/RankOne.lean`](lean/MagicSquares/RankOne.lean) contains the whole argument,
from "nine squares in a magic square" to "rank at least 2". It uses Mathlib, Lean's large library of standard
mathematics, which already contains the curve's point-addition rule.

**Two facts are taken as given.** Both come from the literature and are written out as explicit assumptions in
the theorem's statement, so anyone reading it sees exactly what is assumed:
1. **The "new prime" theorem** of Voutier and Yabuta, with Verzobio's fix (Step 4).
2. **The four small points.** The curves y² = x³ − n²x have only four points of finite order: the point at
   infinity and (0, 0), (n, 0), (−n, 0). This is a classical textbook fact (Koblitz's book, Chapter I).

Everything else is checked by the computer, including:
- the halving formula, which shows each of the three points is twice another point;
- the doubling formula, which shows doubled points have square x-coordinates;
- the "new prime can't cancel" argument of Step 5;
- the algebra that turns a group which isn't generated by one point into rank at least 2.

Lean's report says the proof uses only its three standard axioms, the same ones behind nearly all of Mathlib.
To check it yourself, follow the build steps in the [README](README.md).

## Glossary

| term | meaning |
|---|---|
| arithmetic progression | numbers with a common gap, such as 1, 25, 49 |
| congruent number curve | the curve y² = x³ − n²x |
| rank | how many independent starting points generate all the curve's points |
| primitive divisor | a prime that divides a term of a sequence and divides no earlier term |
| squarefree part | what's left after removing square factors: 24 = 6 × 2², so its squarefree part is 6 |
| density zero | the fraction of numbers up to N with the property tends to 0 as N grows |
