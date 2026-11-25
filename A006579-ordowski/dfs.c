/*
 * Structured search for squarefree composite n <= X with P(n) == -k (mod n),
 * where P(n) = sum_{j<=n} gcd(j,n) = prod_{p|n} (2p-1) for squarefree n.
 * (k = 1 is Ordowski's conjecture on A006579 / A018804; other k are for cross-checks.)
 *
 * Write n = m*q with q the largest prime factor, g = gpf(m) < q, Pm = P(m).
 * Then P(n) = Pm*(2q-1), and P(n) == -k (mod n) iff
 *    (a) mod q:  Pm*(-1) == -k, i.e. q | Pm - k
 *    (b) mod m:  Pm*(2q-1) == -k, which fixes q in one residue class mod m (or m/2).
 * Enumerate squarefree m by DFS over primes with m*g < X (room for some q > g).
 * For m <= T: q ranges over the prime factors of D = Pm - k (trial division).
 * For m >  T: q runs over the residue class from (b) in (g, X/m]: about 2X/m^2 values.
 *
 * Usage: dfs X [k] [T]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <omp.h>

typedef unsigned __int128 u128;
static uint32_t *pr; static size_t npr;
static uint64_t X, T; static int64_t K;
static uint64_t nodes = 0, hits = 0;

static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
static int isprime(uint64_t n) {
    if (n < 2) return 0;
    static const uint64_t sp[] = {2,3,5,7,11,13,17,19,23,29,31,37};
    for (int i = 0; i < 12; i++) { if (n % sp[i] == 0) return n == sp[i]; }
    uint64_t d = n - 1; int s = 0; while (!(d & 1)) { d >>= 1; s++; }
    for (int i = 0; i < 12; i++) {
        uint64_t x = powmod(sp[i], d, n);
        if (x == 1 || x == n - 1) continue;
        int ok = 0;
        for (int r = 1; r < s; r++) { x = mulmod(x, x, n); if (x == n - 1) { ok = 1; break; } }
        if (!ok) return 0;
    }
    return 1;
}
/* inverse of a mod m (gcd must be 1), returns 0 if not invertible */
static uint64_t invmod(uint64_t a, uint64_t m) {
    int64_t t = 0, nt = 1; uint64_t r = m, nr = a % m;
    while (nr) {
        uint64_t q = r / nr;
        int64_t tt = t - (int64_t)q * nt; t = nt; nt = tt;
        uint64_t rr = r - q * nr; r = nr; nr = rr;
    }
    if (r != 1) return 0;
    if (t < 0) t += (int64_t)m;
    return (uint64_t)t;
}

static void report(uint64_t m, uint64_t q, uint64_t Pm) {
    uint64_t n = m * q;
    u128 full = (u128)Pm * (2 * q - 1);
    if ((full + (u128)K) % n != 0) return;
    #pragma omp critical
    { printf("HIT n=%llu = m*q, m=%llu, q=%llu, (P(n)+%lld)/n = %llu\n",
             (unsigned long long)n, (unsigned long long)m, (unsigned long long)q, (long long)K,
             (unsigned long long)((full + (u128)K) / n)); fflush(stdout); }
    #pragma omp atomic
    hits++;
}

static void process(uint64_t m, uint64_t g, uint64_t Pm) {
    uint64_t Q = X / m;
    if (Q <= g) return;
    if ((int64_t)Pm <= K) return;
    uint64_t D = Pm - (uint64_t)K;
    if (m <= T) {
        uint64_t d = D;
        for (size_t i = 0; i < npr; i++) {
            uint64_t p = pr[i];
            if (p * p > d) break;
            if (d % p == 0) {
                if (p > g && p <= Q) report(m, p, Pm);
                while (d % p == 0) d /= p;
            }
        }
        if (d > 1 && d > g && d <= Q) report(m, d, Pm);   /* d is prime here (pr covers sqrt(D)) */
        return;
    }
    uint64_t inv = invmod(Pm % m, m);
    if (!inv) return;
    uint64_t c = mulmod((uint64_t)(m - (uint64_t)(K % (int64_t)m)) % m, inv, m);  /* c = -K/Pm mod m */
    uint64_t Mp, q0;
    if (m & 1) { Mp = m; q0 = mulmod((c + 1) % m, (m + 1) / 2, m); }
    else { if (!(c & 1)) return; Mp = m / 2; q0 = ((c + 1) / 2) % Mp; }
    uint64_t q = q0;
    if (q <= g) q += ((g - q) / Mp + 1) * Mp;
    for (; q <= Q; q += Mp) if (D % q == 0 && isprime(q)) report(m, q, Pm);
}

static void dfs(size_t i0, uint64_t m, uint64_t g, uint64_t Pm, int depth) {
    if (m > 1) { process(m, g, Pm);
        #pragma omp atomic
        nodes++;
    }
    for (size_t i = i0; i < npr; i++) {
        uint64_t p = pr[i];
        if ((u128)m * p * (p + 1) > X) break;
        if (depth < 2) {
            #pragma omp task firstprivate(i, p)
            dfs(i + 1, m * p, p, Pm * (2 * p - 1), depth + 1);
        } else dfs(i + 1, m * p, p, Pm * (2 * p - 1), depth + 1);
    }
}

int main(int argc, char **argv) {
    X = strtoull(argv[1], 0, 10);
    K = argc > 2 ? strtoll(argv[2], 0, 10) : 1;
    T = argc > 3 ? strtoull(argv[3], 0, 10) : 2000000;
    /* primes up to max(sqrt(X), sqrt(max D)) ; D < 2^13 * T for the trial-division branch */
    uint64_t lim = (uint64_t)sqrtl((long double)X) + 2;
    uint64_t lim2 = (uint64_t)sqrtl((long double)T * 8192.0L) + 2;
    if (lim2 > lim) lim = lim2;
    char *c = calloc(lim + 1, 1); pr = malloc(sizeof(uint32_t) * (lim / 2 + 16));
    for (uint64_t i = 2; i <= lim; i++) { if (c[i]) continue; pr[npr++] = (uint32_t)i; for (uint64_t j = i * i; j <= lim; j += i) c[j] = 1; }
    free(c);
    double t0 = omp_get_wtime();
    #pragma omp parallel
    #pragma omp single
    dfs(0, 1, 0, 1, 0);
    printf("DONE X=%llu k=%lld T=%llu nodes=%llu hits=%llu time=%.1fs\n", (unsigned long long)X, (long long)K,
           (unsigned long long)T, (unsigned long long)nodes, (unsigned long long)hits, omp_get_wtime() - t0);
    return 0;
}
