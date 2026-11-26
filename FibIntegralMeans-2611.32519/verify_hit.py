# Independent verification of a counterexample candidate m for Conjecture 1.28 (arXiv 2611.32519).
# Claim: n = F_m lies in A = {n >= 2 : n | F_1 + ... + F_n}.  Since F_1+...+F_n = F_{n+2} - 1,
# this means F_{n+2} == 1 (mod F_m).  Lemma (proved below numerically, and by the identities
# F_{k+m} == F_{m+1} F_k (mod F_m), F_{m+1}^2 == -1 (mod F_m) for odd m): F_k == 1 (mod F_m) iff k mod 4m in {1,2,2m-2,4m-1}.
# So it suffices to compute (F_m + 2) mod 4m.
import sys, random
sys.stdout.reconfigure(encoding="utf-8")
def fibpair(n, M):            # (F_n mod M, F_{n+1} mod M) by fast doubling
    a, b = 0, 1
    for bit in bin(n)[2:]:
        c = a * (2 * b - a) % M; d = (a * a + b * b) % M
        a, b = (d, (c + d) % M) if bit == '1' else (c, d)
    return a, b
def is_prp(n, rounds=40):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for _ in range(rounds):
        a = random.randrange(2, n - 1); x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
# sanity check of the lemma against brute force for small odd m
F = [0, 1]
for i in range(2, 400): F.append(F[-1] + F[-2])
for m in range(5, 40, 2):
    for k in range(1, 8 * m):
        assert (F[k] % F[m] == 1 % F[m]) == (k % (4 * m) in (1, 2, 2 * m - 2, 4 * m - 1)), (m, k)
print("lemma check (odd m in [5,39], k < 8m): OK")
# and the full definition for small odd m, directly with big integers
for m in range(5, 26, 2):
    n = F[m]; S = sum(F[1:n + 1]) if n < 400 else None
    if S is not None:
        lhs = (S % n == 0); rhs = ((n + 2) % (4 * m) in (1, 2, 2 * m - 2, 4 * m - 1))
        assert lhs == rhs, m
print("definition check via direct sums (odd m <= 13): OK")
for arg in sys.argv[1:]:
    k, P = map(int, arg.split('*'))
    m = k * P
    fm, _ = fibpair(m, 4 * m)
    r = (fm + 2) % (4 * m)
    t = 4 if m % 3 == 0 else 3
    print(f"m = {k} * {P} = {m}")
    print(f"  P probable prime: {is_prp(P)};  k = {k}; m odd: {m % 2 == 1}; 5 | m: {m % 5 == 0}")
    print(f"  F_m mod m = {fm % m}  (m - {t} = {m - t}) -> m | F_m + {t}: {(fm + t) % m == 0}")
    print(f"  (F_m + 2) mod 4m = {r};  allowed: 1, 2, 2m-2, 4m-1 -> {'IN A (counterexample)' if r in (1, 2, 2*m-2, 4*m-1) else 'not in A'}")
