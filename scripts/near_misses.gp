\\ Remark 5.3: two full b-progressions give two of the three points P_alpha on E_n.
\\ Run with PARI/GP 2.17:   gp -q near_misses.gp > near_misses.out
\\
\\ Part 1. Two full b-progressions can give dependent points, even in a magic square with nine distinct
\\ entries: an example with six square entries on the rank-one curve E_6.
\\
\\ Part 2. In Bremner's seven-square magic square, and in each of the 2,320 six-square configurations in
\\ near_misses_data.gp, the two points are independent. The proof is exact; it uses no heights.
\\   * Each point is P = 2R, with R from the halving formula behind Lemma 2.1(b).
\\   * The 2-descent map phi(x, y) = (x, x - n) modulo squares, with phi(0, 0) = (-1, -n) and
\\     phi(n, 0) = (n, 2), is an injective homomorphism E_n(Q)/2E_n(Q) -> (Q*/Q*^2)^2 (Silverman,
\\     The Arithmetic of Elliptic Curves, Prop. X.1.4).
\\   * If phi(R1), phi(R2), phi(0, 0), phi(n, 0) are linearly independent over F_2, then R1 and R2 are
\\     independent modulo E_n(Q)_tors = E_n[2] (Lemma 2.1(a)), so P1 = 2 R1 and P2 = 2 R2 are independent.
\\   * Otherwise a relation puts W = c1 R1 + c2 R2 + c3 (0, 0) + c4 (n, 0) in 2E_n(Q), with c1 or c2 odd.
\\     Replacing R1 (if c1 is odd) or R2 by a half of W does not change whether the pair is independent,
\\     and the test is repeated.

read("near_misses_data.gp");

\\ The squarefree integer in the class of a nonzero rational q modulo squares.
sqc(q) = core(numerator(q) * denominator(q));

\\ Points of E_n are [x, y]; [0] is the point at infinity O.

\\ The point of E_n from a full b-progression with middle entry M, where |b| = n k^2.
bpoint(M, n, k) =
{
  my(X = M / k^2, Y);
  if (!issquare(X * (X - n) * (X + n), &Y), error("not a point: ", M));
  [X, Y];
}

\\ The 2-descent map phi.
phi(P, n) =
{
  if (#P == 1, return([1, 1]));
  if (P[1] == 0, return([-1, -n]));
  if (P[1] == n, return([n, 2]));
  [sqc(P[1]), sqc(P[1] - n)];
}

\\ The F_2-matrix whose columns are the classes in L; each class is a pair of squarefree integers.
f2mat(L) =
{
  my(ps = [], N, M);
  for (c = 1, #L, for (j = 1, 2, ps = setunion(ps, Set(factor(abs(L[c][j]))[, 1]~))));
  N = #ps + 1;
  M = matrix(2 * N, #L);
  for (c = 1, #L,
    for (j = 1, 2,
      my(q = L[c][j]);
      M[(j - 1) * N + 1, c] = (q < 0);
      for (s = 1, #ps, M[(j - 1) * N + 1 + s, c] = valuation(q, ps[s]))));
  Mod(M, 2);
}

\\ A point R with 2R = P, for P in 2E_n(Q): x(P), x(P) - n and x(P) + n are squares r1^2, r2^2, r3^2,
\\ with signs chosen so that r1 r2 r3 = y(P), and R = ((r1 + r2)(r1 + r3), (r1 + r2)(r1 + r3)(r2 + r3)).
half(C, n, P) =
{
  my(r1, r2, r3, R);
  if (#P == 1 || !issquare(P[1], &r1) || !issquare(P[1] - n, &r2) || !issquare(P[1] + n, &r3),
    error("not in 2E_n(Q): ", P));
  if (r1 * r2 * r3 != P[2], r3 = -r3);
  R = [(r1 + r2) * (r1 + r3), (r1 + r2) * (r1 + r3) * (r2 + r3)];
  if (ellmul(C, R, 2) != P, error("halving failed: ", P));
  R;
}

\\ Certify that P1, P2 in 2E_n(Q) are independent. Returns the number of replacement steps needed, or -1
\\ if 10 steps do not suffice (which does not happen below).
certify(n, P1, P2) =
{
  my(C = ellinit([0, 0, 0, -n^2, 0]), T1 = [0, 0], T2 = [n, 0], U, V);
  U = half(C, n, P1);
  V = half(C, n, P2);
  for (step = 0, 10,
    my(M = f2mat([phi(U, n), phi(V, n), phi(T1, n), phi(T2, n)]), c, W);
    if (matrank(M) == 4, return(step));
    c = lift(matker(M)[, 1]);
    W = elladd(C, elladd(C, ellmul(C, U, c[1]), ellmul(C, V, c[2])),
               elladd(C, ellmul(C, T1, c[3]), ellmul(C, T2, c[4])));
    if (W == [0], return(-1));
    if (c[1], U = half(C, n, W), V = half(C, n, W)));
  -1;
}

\\ An entry, written as r^2 when it is a square.
fmt(x) = my(r); if (issquare(x, &r), Str(r, "^2"), Str(x));

print("== Part 1: E = 1201^2, a = 1319901, b = 117600 = 6 * 140^2");
{
  my(E = 1201^2, a = 1319901, b = 117600, L, v, C = ellinit([0, 0, 0, -36, 0]), G = [-3, 9], H, Pm, P0);
  L = [E + a, E - a - b, E + b; E - a + b, E, E + a - b; E - b, E + a + b, E - a];
  for (i = 1, 3, printf("  %10s %10s %10s\n", fmt(L[i, 1]), fmt(L[i, 2]), fmt(L[i, 3])));
  v = concat(vector(3, i, L[i, ]));
  print("  line sums: ", Set(concat([vector(3, i, vecsum(L[i, ])), vector(3, j, vecsum(L[, j]~)),
    [L[1, 1] + L[2, 2] + L[3, 3], L[1, 3] + L[2, 2] + L[3, 1]]])));
  print("  distinct entries: ", #Set(v), "; positive: ", #select(t -> t > 0, v),
    "; square entries: ", #select(issquare, v), "; gcd: ", content(v));
  print("  b-progressions E + alpha a - b, E + alpha a, E + alpha a + b, by number of squares:");
  for (al = -1, 1, printf("    alpha = %2d: %d\n", al, #select(issquare, vector(3, j, E + al * a + (j - 2) * b))));
  setrand(1);
  print("  rank bounds for E_6 from ellrank: ", ellrank(C)[1..2]);
  H = ellmul(C, G, 2);
  Pm = bpoint(E - a, 6, 140);
  P0 = bpoint(E, 6, 140);
  print("  G = ", G, ", H = 2G = ", H);
  print("  x(P_-1) = ", Pm[1], " = x(H): ", Pm[1] == H[1]);
  print("  x(P_0) = ", P0[1], " = x(2H): ", P0[1] == ellmul(C, H, 2)[1]);
  print("  so P_-1 = +-H and P_0 = +-2H are dependent.");
  print("  control: the test of Part 2 does not certify this pair: ", certify(6, Pm, P0) < 0);
}

print();
print("== Part 2: Bremner's square, E = 425^2, a = -41496, b = 138600 = 154 * 30^2");
{
  my(E = 425^2, a = -41496, b = 138600, n = core(b), k = sqrtint(b / n));
  printf("  full b-progressions alpha = 0, 1 on E_%d: independent (replacement steps: %d)\n",
    n, certify(n, bpoint(E, n, k), bpoint(E + a, n, k)));
}

print();
print("== Part 2: the stored configurations, with full b-progressions alpha = +-1");
{
  my(bad = 0, sq = 0, cnt = vector(11), fail = 0);
  for (i = 1, #NM,
    my([E, a, b] = NM[i]);
    my(n = core(abs(b)), k, s);
    k = sqrtint(abs(b) / n);
    for (al = -1, 1, if (al, for (be = -1, 1, if (!issquare(E + al * a + be * b), bad++))));
    if (issquare(E), sq++);
    s = certify(n, bpoint(E - a, n, k), bpoint(E + a, n, k));
    if (s < 0, fail++, cnt[s + 1]++);
    if (s != 0, printf("  configuration %d, n = %d: replacement steps: %d\n", i, n, s)));
  print("  configurations: ", #NM, "; failed square checks: ", bad, "; square centers: ", sq);
  print("  independent, by number of replacement steps:");
  for (s = 0, 10, if (cnt[s + 1], printf("    %d: %d configuration%s\n", s, cnt[s + 1], if (cnt[s + 1] == 1, "", "s"))));
  print("  not certified: ", fail);
}
quit;
