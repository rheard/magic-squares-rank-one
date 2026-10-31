\\ Every computation in "Magic squares of squares and elliptic divisibility sequences: the rank-one case".
\\ Run with PARI/GP 2.17:   gp -q checks.gp > checks.out
\\ It takes under a minute; checks.out is the output we got.
\\ Throughout, E_n is the congruent number curve y^2 = x^3 - n^2 x.

default(parisize, 512*10^6);
\\ ellrank searches for points at random; fix the seed so that the output is reproducible.
setrand(1);
En(n) = ellinit([0, 0, 0, -n^2, 0]);

print("== Lemma 2.1(d): y^2 = x^3 - n^2 x is a minimal model for every squarefree n <= 2000");
{
  my(cnt = 0, bad = 0);
  forsquarefree(nn = 1, 2000,
    my(n = nn[1], v);
    ellminimalmodel(En(n), &v);
    cnt++;
    if(v[1] != 1, bad++; print("  not minimal: n = ", n)));
  print("  checked ", cnt, " values of n; non-minimal models: ", bad);
}

print();
print("== Corollary 1.2, density: E_1 has full 2-torsion and no rational cyclic subgroup of order 4");
E1 = En(1);
print("  torsion structure of E_1(Q): ", elltors(E1)[2]);
print("  x-coordinates of the nonzero 4-torsion points are the roots of ", factor(elldivpol(E1, 4)));
print("  (the linear factors give the 2-torsion; the quadratics give the points of order 4)");
print("  degrees of the isogenies from E_1: ", ellisomat(E1)[2][1,]);

print();
print("== Corollary 1.2, list: squarefree n <= 150 with rank E_n(Q) >= 2");
{
  my(two = [], undecided = []);
  forsquarefree(nn = 1, 150,
    my(n = nn[1], R = ellrank(En(n)));
    if(R[1] >= 2, two = concat(two, n),
      if(R[2] >= 2, undecided = concat(undecided, [[n, R[1], R[2]]]))));
  print("  rank >= 2 proved for n = ", two);
  print("  rank <= 1 proved for every other n, except [n, lower, upper] = ", undecided);
}
\\ Tunnell: if an odd squarefree n is congruent, then #{x^2+2y^2+8z^2 = n} = 2 #{x^2+2y^2+32z^2 = n}.
reps(n, c) =
{
  my(s = 0);
  for(x = -sqrtint(n), sqrtint(n),
    for(y = -sqrtint(n \ 2), sqrtint(n \ 2),
      my(r = n - x^2 - 2*y^2);
      if(r >= 0 && r % c == 0 && issquare(r / c), s += if(r == 0, 1, 2))));
  s;
}
print("  Tunnell counts for n = 113: ", reps(113, 8), " and ", reps(113, 32), ", so 113 is not congruent");

print();
print("== Example 1.3: E_6 has rank one, and x(2G) = 25/4");
E6 = En(6);
print("  rank bounds for E_6: ", ellrank(E6)[1..2]);
G6 = ellsaturation(E6, ellrank(E6)[4], 100)[1];
print("  generator G = ", G6, ", x(2G) = ", ellmul(E6, G6, 2)[1]);
print("  the multiples mH of H = 2G, with the primes new to each denominator:");
{
  my(H = ellmul(E6, G6, 2), seen = []);
  for(m = 1, 5,
    my(x = ellmul(E6, H, m)[1], k = sqrtint(denominator(x)), v = sqrtint(numerator(x)));
    my(f = Set(factor(k)[, 1]~), new = setminus(f, seen));
    seen = setunion(seen, f);
    print("  m = ", m, ": x(mH) = ", v, "^2 / ", k, "^2, new primes ", new));
}

print();
print("== Remark 5.2: Bremner's seven-square magic square, E = 425^2, a = -41496, b = 138600");
{
  my(E = 425^2, a = -41496, b = 138600);
  my(L = matrix(3, 3, i, j, E + (i - 2) * a + (j - 2) * b));
  print("  rows alpha = -1, 0, 1 hold the b-progressions E + alpha a + beta b, beta = -1, 0, 1:");
  for(i = 1, 3, print("    ", L[i, ], "  squares: ", vector(3, j, issquare(L[i, j]))));
  print("  sqf(b) = ", core(b), ", rank bounds ", ellrank(En(core(b)))[1..2]);
  print("  sqf(a) = ", core(abs(a)), ", rank bounds ", ellrank(En(core(abs(a))))[1..2]);
}

print();
print("== Remark 5.5: Lemma 3.1 on the rank-one curves E_n with squarefree n <= 400");
\\ For each such n, let G generate E_n(Q) modulo torsion and H = 2G. Check that no three of
\\ x(H), ..., x(16H) are in arithmetic progression, and that every B_m(H) with 2 <= m <= 16 has a
\\ primitive divisor, where x(mH) = A_m / B_m^2 in lowest terms.
MMAX = 16;
Bden(x) = sqrtint(denominator(x));
\\ remove from g every prime factor of h
strip(g, h) = { my(d); while((d = gcd(g, h)) > 1, g /= d); g; }
has_primitive(Bv, m) =
{
  my(g = Bv[m]);
  for(d = 1, m - 1, g = strip(g, Bv[d]));
  g > 1;
}
{
  my(nrank1 = 0, undecided = 0, nopoint = [], bad_ap = 0, bad_prim = 0);
  forsquarefree(nn = 1, 400,
    my(n = nn[1], E = En(n), R = ellrank(E), G, H, X, Bv);
    if(R[1] != R[2], undecided++; next);
    if(R[1] != 1, next);
    if(#R[4] < 1, R = ellrank(E, 2));
    if(#R[4] < 1, nopoint = concat(nopoint, n); next);
    nrank1++;
    G = ellsaturation(E, R[4], 100)[1];
    H = ellmul(E, G, 2);
    X = vector(MMAX, m, ellmul(E, H, m)[1]);
    Bv = vector(MMAX, m, Bden(X[m]));
    for(i = 1, MMAX, for(j = i + 1, MMAX, for(c = 1, MMAX,
      if(c != i && c != j && X[i] + X[j] == 2 * X[c],
        bad_ap++; print("  progression found: n = ", n, ", indices ", [i, j, c])))));
    for(m = 2, MMAX,
      if(!has_primitive(Bv, m), bad_prim++; print("  no primitive divisor: n = ", n, ", m = ", m))));
  print("  rank proved to be one, with a generator found, for ", nrank1, " curves");
  print("  rank proved to be one, but no generator found, for n = ", nopoint);
  print("  rank not decided for ", undecided, " curves");
  print("  progressions found: ", bad_ap, "; terms B_m(H), 2 <= m <= 16, without a primitive divisor: ",
    bad_prim);
}

quit;
