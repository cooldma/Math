"""Reference check of the reduction used for Conjecture 1.28 (arXiv 2611.32519).
A = {n >= 2 : n | F_1+...+F_n} = {n : F_{n+2} == 1 (mod n)}.
Claim: for odd m >= 5, F_m in A  <=>  m | F_m + 3 (3 !| m)  or  m | F_m + 4 (3 | m).
Checks the claim against the definition with exact big integers, and checks the
even-m list F_12, F_24, F_34, ... from the paper."""
import sys
def fib_pair(k, mod=None):
    # returns (F_k, F_{k+1}) [mod mod]
    a, b = 0, 1
    for bit in bin(k)[2:]:
        c = a * (2 * b - a); d = a * a + b * b
        if mod: c %= mod; d %= mod
        a, b = (d, c + d) if bit == '1' else (c, d)
        if mod: b %= mod
    return a, b
def in_A_def(n):          # definition: n | sum_{i<=n} F_i = F_{n+2} - 1
    return n >= 2 and fib_pair(n + 2, n)[0] % n == 1 % n
M = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
F = [0, 1]
while len(F) <= M: F.append(F[-1] + F[-2])
bad = 0; evenA = []
for m in range(3, M + 1):
    Fm = F[m]
    member = in_A_def(Fm)
    if m % 2:
        crit = (Fm + (4 if m % 3 == 0 else 3)) % m == 0
        if m >= 5 and member != crit: bad += 1; print('MISMATCH odd', m)
        if m >= 5 and member: print('COUNTEREXAMPLE', m)
    else:
        crit = Fm % (2 * m) in (0, 2 * m - 1, 2 * m - 3)
        if m >= 4 and member != crit: bad += 1; print('MISMATCH even', m)
        if member: evenA.append(m)
print('even m with F_m in A (m<=%d):' % M, evenA[:12], '... total', len(evenA))
# weaker test with other offsets, to show the criterion machinery finds real hits
for c in (1, -1, 2, -2, 3, 4, 7):
    hits = [m for m in range(5, min(M, 4000) + 1, 2) if (F[m] + c) % m == 0]
    print('odd m<=%d with m | F_m%+d:' % (min(M, 4000), c), len(hits), hits[:10])
print('mismatches:', bad)
