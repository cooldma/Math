/*
 * Smallest counterexample to Ordowski's conjecture on OEIS A006579 / A018804.
 *
 * P(n) = sum_{k=1..n} gcd(k,n) (A018804),  A006579(n) = P(n) - n.
 * Conjecture: for composite n, P(n) != -1 (mod n).
 * Known counterexample: n = 23492890653051 = 3*37*43*42307*116341.
 *
 * Reduction: if p^2 | n then p | P(n), so a counterexample is squarefree,
 * and for squarefree n, P(n) = prod_{p|n} (2p-1) exactly.
 * So we test, for squarefree composite n in [lo, hi], whether
 * prod_{p|n} (2p-1) + 1 == 0 (mod n).  The product is < 2^omega(n) * n,
 * which fits in 64 bits for n < 1e15.
 *
 * Segmented sieve: for each block, multiply in p and (2p-1) for every
 * prime p <= sqrt(hi); the leftover cofactor n / prod(p) is 1 or one prime.
 *
 * Usage: search lo hi [k]      (search for P(n) == -k mod n, default k = 1)
 *        search test N         (compare with brute-force gcd sums, n <= N)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <omp.h>

#ifndef BLOCK
#define BLOCK (1u << 18)
#endif
typedef struct { uint64_t pp, fp; } cell;

static uint32_t *primes;
static size_t nprimes;

static void make_primes(uint64_t lim) {
    char *c = calloc(lim + 1, 1);
    primes = malloc(sizeof(uint32_t) * (lim / 2 + 16));
    nprimes = 0;
    for (uint64_t i = 2; i <= lim; i++) {
        if (c[i]) continue;
        primes[nprimes++] = (uint32_t)i;
        for (uint64_t j = i * i; j <= lim; j += i) c[j] = 1;
    }
    free(c);
}

static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: search lo hi | search test N\n"); return 1; }
    int test = strcmp(argv[1], "test") == 0;
    uint64_t lo = test ? 1 : strtoull(argv[1], 0, 10);
    uint64_t hi = strtoull(argv[2], 0, 10);
    int64_t K = argc > 3 ? strtoll(argv[3], 0, 10) : 1;
    if (lo < 2) lo = 2;
    uint64_t sq = (uint64_t)sqrtl((long double)hi) + 2;
    make_primes(sq);
    uint64_t nblocks = (hi - lo) / BLOCK + 1;
    uint64_t hits = 0, sqf_comp = 0, mism = 0, blocks_done = 0;
    double t0 = omp_get_wtime();

    #pragma omp parallel reduction(+:hits,sqf_comp,mism)
    {
        cell *c = malloc(sizeof(cell) * BLOCK);
        #pragma omp for schedule(dynamic, 1)
        for (uint64_t b = 0; b < nblocks; b++) {
            uint64_t L = lo + b * BLOCK;
            if (L > hi) continue;
            uint64_t R = L + BLOCK - 1; if (R > hi) R = hi;
            uint32_t len = (uint32_t)(R - L + 1);
            for (uint32_t i = 0; i < len; i++) { c[i].pp = 1; c[i].fp = 1; }
            for (size_t k = 0; k < nprimes; k++) {
                uint64_t p = primes[k];
                if (p * p > R) break;
                uint64_t m = ((L + p - 1) / p) * p;
                uint64_t f = 2 * p - 1;
                for (uint64_t x = m - L; x < len; x += p) { c[x].pp *= p; c[x].fp *= f; }
                uint64_t p2 = p * p;
                uint64_t m2 = ((L + p2 - 1) / p2) * p2;
                for (uint64_t x = m2 - L; x < len; x += p2) c[x].pp = 0;   /* not squarefree */
            }
            for (uint32_t i = 0; i < len; i++) {
                if (c[i].pp == 0) continue;
                uint64_t n = L + i;
                uint64_t r = n / c[i].pp;
                uint64_t full = c[i].fp;
                if (r > 1) full *= (2 * r - 1);
                /* for squarefree n, prod(2p-1) == 2n-1 iff n is prime (trivial case) */
                if (full == 2 * n - 1) continue;
                sqf_comp++;
                if (test) {
                    uint64_t s = 0;
                    for (uint64_t k = 1; k <= n; k++) s += gcd64(k, n);
                    if (s != full) {
                        #pragma omp critical
                        printf("MISMATCH n=%llu brute=%llu sieve=%llu\n",
                               (unsigned long long)n, (unsigned long long)s, (unsigned long long)full);
                        mism++;
                    }
                }
                if ((full + (uint64_t)K) % n == 0) {
                    #pragma omp critical
                    { printf("HIT n=%llu  P(n)+1 = %llu * n\n", (unsigned long long)n,
                             (unsigned long long)((full + (uint64_t)K) / n)); fflush(stdout); }
                    hits++;
                }
            }
            #pragma omp atomic
            blocks_done++;
            if (omp_get_thread_num() == 0 && blocks_done % 4096 == 0) {
                fprintf(stderr, "progress %.3f%%  %.0fs\n", 100.0 * blocks_done / nblocks, omp_get_wtime() - t0);
            }
        }
        free(c);
    }
    printf("DONE lo=%llu hi=%llu squarefree_composites=%llu hits=%llu mismatches=%llu time=%.1fs\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)sqf_comp,
           (unsigned long long)hits, (unsigned long long)mism, omp_get_wtime() - t0);
    return 0;
}
