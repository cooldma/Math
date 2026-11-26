/*
 * fibsearch2.c - fast exhaustive search for counterexamples to Conjecture 1.28 of
 *   S. Mandal, Mohan, "Integral Means of Fibonacci Numbers: Divisibility,
 *   Density, and Arithmetic Structure", arXiv:2611.32519 (24 Nov 2026):
 *       "If m >= 5 is odd, then F_m is not in A",  A = {n : n | F_1+...+F_n}.
 *
 * Reduction (paper's Lemma 2.18(2) + CRT; checked against the definition in ref.py):
 *   for odd m >= 5:  F_m in A  <=>  m | F_m + 3 (3 !| m)   or   m | F_m + 4 (3 | m).
 *
 * Search over odd m in [lo, hi), m < 2^62.  One byte per odd m, two nibbles:
 *   low  nibble  = (#primes p|m whose local test fails)    -> m rejected if != 0
 *   high nibble  = (#primes p|m, p <= sqrt(hi))            -> 0 means m is prime
 *   local test at p:  F_m == -t (mod p), t = tA (3!|m) or tB (3|m); since F_m mod p
 *   depends only on m mod pi(p) (Pisano period) this is a residue condition.
 *   - p in {3,5,7,11,13}: precomputed periodic pattern (period 120120 in odd index)
 *   - 17 <= p <= B      : "+0x11" at every odd multiple of p, then "-0x01" on the
 *                         CRT progressions m == 0 (p), m == r (pi(p)), m mod 6 fixed,
 *                         for every good r (F_r == -t mod p).  Order: adds first.
 *   - B < p <= sqrt(hi) : "+0x10" from p^2 on (compositeness only)
 *   Primes p > 2^19 index-stride are bucket-sieved (at most one hit per block).
 * Survivors (low nibble 0, high nibble != 0) are tested exactly with a branch-free
 * Lucas V ladder in Montgomery arithmetic, 8 interleaved lanes:
 *   2 V_{m+1} - V_m = 5 F_m,  so test 5F_m == -5t (mod m)   (5 | m handled apart).
 *
 * Usage: fibsearch2 lo hi [-t threads] [-B bound] [-c tA tB] [-noprimeskip]
 *                         [-list] [-chunk log2] [-ckpt file]
 * Build: gcc -O3 -march=native -funroll-loops -fopenmp -o fibsearch2 fibsearch2.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
#include <immintrin.h>

typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128; typedef __int128 i128;

static i64 tA = 3, tB = 4;
static int primeskip = 1, listall = 0, usefilter = 1;
static u64 B = 1u << 20;

#define BLKLOG 18
#define BLK (1u << BLKLOG)              /* odd numbers per block (bytes) */
#ifndef SUBLOG
#define SUBLOG 14
#endif
#define SUB (1u << SUBLOG)              /* L1 sub-block for primes < SUB */
#define PER 120120u                     /* pattern period for p in {3,5,7,11,13} */
static uint8_t pattern[PER];

static i64 posmod(i64 a, i64 p) { a %= p; return a < 0 ? a + p : a; }

/* ---------------- primes ---------------- */
static uint32_t *primes; static size_t nprimes;  /* odd primes >= 17 up to max(B, sqrt hi) */
static size_t nmed;                             /* primes[0..nmed) are <= B */

static void make_primes(u64 lim) {
    uint8_t *s = calloc(lim + 1, 1); size_t cnt = 0;
    for (u64 i = 2; i * i <= lim; i++) if (!s[i]) for (u64 j = i * i; j <= lim; j += i) s[j] = 1;
    for (u64 i = 17; i <= lim; i++) cnt += !s[i];
    primes = malloc((cnt + 1) * sizeof *primes); nprimes = 0;
    for (u64 i = 17; i <= lim; i++) if (!s[i]) primes[nprimes++] = (uint32_t)i;
    free(s);
}

/* ---------------- good progressions ---------------- */
typedef struct { u64 a, M; } prog_t;           /* m == a (mod M), M even, a odd */
static prog_t *progs; static size_t nprogs;

static u64 inv_mod(u64 a, u64 n) {               /* a^{-1} mod n, gcd = 1 */
    i64 t = 0, nt = 1; i64 r = (i64)n, nr = (i64)(a % n);
    while (nr) { i64 q = r / nr, tmp; tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
    return (u64)(t < 0 ? t + (i64)n : t);
}
static u64 gcdu(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }
/* combine x == a1 (n1), x == a2 (n2); returns 0 if incompatible */
static int crt(u64 a1, u64 n1, u64 a2, u64 n2, u64 *a, u64 *n) {
    u64 g = gcdu(n1, n2);
    i64 d = (i64)a2 - (i64)a1;
    if (posmod(d, (i64)g)) return 0;
    u64 n2g = n2 / g, l = n1 / g * n2;
    u64 k = (u64)((i128)posmod(d / (i64)g, (i64)n2g) * inv_mod((n1 / g) % n2g ? (n1 / g) % n2g : 1, n2g) % n2g);
    if (n2g == 1) k = 0;
    *a = (u64)(((u128)a1 + (u128)k * n1) % l); *n = l; return 1;
}

static void make_progs(void) {
    nmed = 0; while (nmed < nprimes && primes[nmed] <= B) nmed++;
    size_t cap = 16 * nmed + 16;
    progs = malloc(cap * sizeof *progs); nprogs = 0;
    #pragma omp parallel
    {
        u64 *ja = malloc(64 * sizeof(u64)), *jb = malloc(64 * sizeof(u64));
        #pragma omp for schedule(dynamic, 64)
        for (size_t i = 0; i < nmed; i++) {
            u64 p = primes[i], ta = posmod(-tA, p), tb = posmod(-tB, p);
            int na = 0, nb = 0;
            u64 a = 0, b = 1, n = 0;
            do {
                if (a == ta && na < 64) ja[na++] = n;
                if (a == tb && nb < 64) jb[nb++] = n;
                u64 c = a + b; if (c >= p) c -= p; a = b; b = c; n++;
            } while (!(a == 0 && b == 1));
            u64 pi = n;
            prog_t loc[3 * 128]; int nl = 0;
            /* A-type: m == 1 or 5 (mod 6); B-type: m == 3 (mod 6) */
            for (int q = 0; q < na; q++) for (int c6 = 1; c6 <= 5; c6 += 4) {
                u64 x, X, y, Y;
                if (!crt(0, p, (u64)c6, 6, &x, &X)) continue;
                if (!crt(x, X, ja[q], pi, &y, &Y)) continue;
                loc[nl].a = y; loc[nl].M = Y; nl++;
            }
            for (int q = 0; q < nb; q++) {
                u64 x, X, y, Y;
                if (!crt(0, p, 3, 6, &x, &X)) continue;
                if (!crt(x, X, jb[q], pi, &y, &Y)) continue;
                loc[nl].a = y; loc[nl].M = Y; nl++;
            }
            if (na >= 64 || nb >= 64) { fprintf(stderr, "too many residues p=%llu\n", (unsigned long long)p); exit(1); }
            #pragma omp critical(pg)
            {
                if (nprogs + nl > cap) { cap = 2 * cap + nl; progs = realloc(progs, cap * sizeof *progs); }
                memcpy(progs + nprogs, loc, nl * sizeof *loc); nprogs += nl;
            }
        }
        free(ja); free(jb);
    }
}

/* pattern for p in {3,5,7,11,13}: index i <-> m = 1 + 2i */
static void make_pattern(void) {
    const u64 tp[5] = {3, 5, 7, 11, 13};
    for (u64 i = 0; i < PER; i++) {
        u64 m = 1 + 2 * i; uint8_t v = 0; int bad = 0;
        i64 t = (m % 3 == 0) ? tB : tA;
        for (int k = 0; k < 5; k++) {
            u64 p = tp[k];
            if (m % p) continue;
            v += 0x10;                      /* high nibble counts distinct tiny primes */
            /* F_m mod p by walking (p tiny) */
            u64 a = 0, b = 1, n = 0, per = 0;
            do { u64 c = (a + b) % p; a = b; b = c; n++; } while (!(a == 0 && b == 1));
            per = n; a = 0; b = 1;
            for (u64 j = 0; j < m % per; j++) { u64 c = (a + b) % p; a = b; b = c; }
            if (a != (u64)posmod(-t, (i64)p)) bad = 1;
        }
        pattern[i] = v | (uint8_t)bad;
    }
}

/* ---------------- Montgomery / Lucas kernel ---------------- */
static inline u64 inv64(u64 m) { u64 x = m; for (int i = 0; i < 5; i++) x *= 2 - m * x; return x; }
static inline u64 redc(u128 T, u64 m, u64 minv) {
    u64 lo = (u64)T, hi = (u64)(T >> 64), q = lo * minv, h = (u64)(((u128)q * m) >> 64), r = hi - h;
    return hi < h ? r + m : r;
}
static inline u64 addm(u64 a, u64 b, u64 m) { u64 s = a + b; return s >= m ? s - m : s; }
static inline u64 subm(u64 a, u64 b, u64 m) { return a >= b ? a - b : a + m - b; }
static inline u64 csel(u64 c, u64 a, u64 b) { return c ? a : b; }

#define LANES 2
static void lucas8p(const u64 *m, u64 *res) {      /* res[k] = 5 F_m mod m  (plain) */
    u64 minv[LANES], one[LANES], two[LANES], V0[LANES], V1[LANES], par[LANES];
    for (int k = 0; k < LANES; k++) {
        u64 mk = m[k];
        minv[k] = inv64(mk); one[k] = (0 - mk) % mk; two[k] = addm(one[k], one[k], mk);
        V0[k] = one[k]; V1[k] = addm(two[k], one[k], mk); par[k] = 1;
    }
    int nb = 63 - __builtin_clzll(m[0]);
    for (int i = nb - 1; i >= 0; i--) {
        #pragma GCC unroll 8
        for (int k = 0; k < LANES; k++) {
            u64 mk = m[k], bit = (mk >> i) & 1, s = par[k];
            u64 x = csel(bit, V1[k], V0[k]);
            u64 sq = redc((u128)x * x, mk, minv[k]);
            u64 pr = redc((u128)V0[k] * V1[k], mk, minv[k]);
            sq = ((s ^ bit) & 1) ? addm(sq, two[k], mk) : subm(sq, two[k], mk);
            pr = s ? addm(pr, one[k], mk) : subm(pr, one[k], mk);
            V0[k] = csel(bit, pr, sq); V1[k] = csel(bit, sq, pr); par[k] = bit;
        }
    }
    for (int k = 0; k < LANES; k++) {
        u64 mk = m[k], a = subm(addm(V1[k], V1[k], mk), V0[k], mk);
        res[k] = redc((u128)a, mk, minv[k]);
    }
}

static u64 fib_plain(u64 n, u64 M) {                 /* F_n mod M, plain 128-bit */
    u64 a = 0, b = 1;
    for (int i = 63 - __builtin_clzll(n); i >= 0; i--) {
        u64 c = (u64)(((u128)a * ((2 * (u128)b + M - a) % M)) % M);
        u64 d = (u64)(((u128)a * a + (u128)b * b) % M);
        if ((n >> i) & 1) { a = d; b = (u64)(((u128)c + d) % M); } else { a = c; b = d; }
    }
    return a;
}

static u64 nhits = 0;
static void report(u64 m) {
    i64 t = (m % 3 == 0) ? tB : tA;
    int ok = (fib_plain(m, m) + (u64)posmod(t, (i64)m)) % m == 0, ok4 = -1;
    if (tA == 3 && tB == 4 && m < ((u64)1 << 61))
        ok4 = fib_plain(m, 4 * m) == ((m % 3 == 0) ? 2 * m - 4 : 4 * m - 3);
    #pragma omp critical(rep)
    {
        nhits++;
        printf("HIT m=%llu (m%%3=%d) verify_mod_m=%d verify_mod_4m=%d\n", (unsigned long long)m, (int)(m % 3), ok, ok4);
        fflush(stdout);
    }
}

static void test_batch(const u64 *cb, int n) {
    u64 mm[LANES], res[LANES]; int k2 = 0;
    for (int q = 0; q < n; q++) {
        u64 m = cb[q];
        if (m % 5 == 0) { i64 t = (m % 3 == 0) ? tB : tA; if ((fib_plain(m, m) + (u64)posmod(t, (i64)m)) % m == 0) report(m); }
        else mm[k2++] = m;
    }
    if (!k2) return;
    for (int q = k2; q < LANES; q++) mm[q] = mm[0];
    lucas8p(mm, res);
    for (int q = 0; q < k2; q++) {
        u64 m = mm[q]; i64 t = (m % 3 == 0) ? tB : tA;
        if (res[q] == (u64)posmod(-5 * t, (i64)m)) report(m);
    }
}

/* ---------------- cofactor prefilter ----------------
 * Survivor m with high nibble h = #distinct primes p <= sqrt(hi) dividing m that the
 * sieve saw (tiny ones always; medium p <= B at every multiple; large p from p^2 on).
 * Strip the tiny primes 3,7,11,13 (5 | m is always rejected): m = s * r.  If that
 * accounts for all h primes, r has no prime factor <= B, and if r were composite its
 * least prime q satisfies q <= sqrt(m) <= sqrt(hi), q^2 <= m, so q would be counted.
 * Hence r is 1 or a prime > B with r !| s.  For prime r != 5, Q^r == Q or -Q^{-1}
 * (mod r) (paper's Lemma 2.19), so F_m = F_{s r} == +-F_s (mod r), and r | F_m + t
 * forces F_s == +-t (mod r).  Checked with an exact table F_s (s <= 186, F_s < 2^128). */
static u128 FIB[187];
static u64 nfilt = 0;           /* informational (racy counter not needed) */
static void make_fib(void) { FIB[0] = 0; FIB[1] = 1; for (int i = 2; i < 187; i++) FIB[i] = FIB[i - 1] + FIB[i - 2]; }
/* returns 1 if m can be discarded */
static inline int prefilter(u64 m, unsigned h) {
    u64 s = 1, r = m; unsigned cnt = 0;
    static const u64 tp[4] = {3, 7, 11, 13};
    for (int k = 0; k < 4; k++) {
        u64 p = tp[k];
        if (r % p == 0) { cnt++; do { r /= p; s *= p; } while (r % p == 0); }
    }
    if (cnt != h || r == 1 || s > 186) return 0;
    i64 t = (m % 3 == 0) ? tB : tA;
    u64 x = (u64)(FIB[s] % r), tp_ = (u64)posmod(t, (i64)r), tn = (u64)posmod(-t, (i64)r);
    return x != tp_ && x != tn;
}

/* ---------------- per-thread chunk worker ---------------- */
typedef struct { u64 idx; uint32_t p; uint32_t nxt; } bent_t;   /* bucket entry */
typedef struct {
    uint8_t *v;                 /* BLK bytes */
    u64 *nx;                    /* next index for small-stride primes */
    u64 *pidx, *pstep;          /* active progressions in this chunk */
    bent_t *be; uint32_t *bhead; size_t nbh;
    u64 cand, tested;
} ws_t;

static void do_chunk(u64 c0, u64 c1, ws_t *w) {
    u64 total = (c1 - c0) / 2;                        /* odd m = c0 + 2 idx, idx < total */
    u64 sq = (u64)sqrtl((long double)(c1)) + 1; while (sq * sq > c1) sq--;
    size_t np = 0; while (np < nprimes && (primes[np] <= sq || np < nmed)) np++;
    u64 nblk = (total + BLK - 1) / BLK;
    if (nblk > w->nbh) { w->bhead = realloc(w->bhead, nblk * sizeof(uint32_t)); w->nbh = nblk; }
    for (u64 b = 0; b < nblk; b++) w->bhead[b] = UINT32_MAX;
    /* primes: start index; small-stride (p < BLK) kept in nx[], others in buckets */
    size_t nsm = 0;
    for (size_t i = 0; i < np; i++) {
        u64 p = primes[i], start = (i < nmed) ? p : p * p;   /* medium: every odd multiple incl. p */
        if (start < c0) { u64 q = (c0 + p - 1) / p; if (!(q & 1)) q++; start = q * p; }
        u64 idx = (start - c0) / 2;
        if (p < BLK) { w->nx[i] = idx; nsm = i + 1; }
        else {
            w->be[i].idx = idx; w->be[i].p = (uint32_t)p;
            if (idx < total) { u64 b = idx >> BLKLOG; w->be[i].nxt = w->bhead[b]; w->bhead[b] = (uint32_t)i; }
        }
    }
    /* progressions active in this chunk */
    size_t na = 0;
    for (size_t j = 0; j < nprogs; j++) {
        u64 M = progs[j].M, a = progs[j].a;
        u64 off = (a >= c0 % M) ? a - c0 % M : a + M - c0 % M;   /* first m >= c0 */
        u64 idx = off / 2;
        if (idx < total) { w->pidx[na] = idx; w->pstep[na] = M / 2; na++; }
    }
    u64 cbuf[LANES]; int nc = 0, nbcur = -1;
    for (u64 bk = 0; bk < nblk; bk++) {
        u64 b0 = bk * BLK, len = total - b0 < BLK ? total - b0 : BLK, bend = b0 + len;
        uint8_t *v = w->v;
        /* 1. pattern copy */
        u64 g = ((c0 + 2 * b0 - 1) / 2) % PER, done = 0;
        while (done < len) { u64 n = PER - g < len - done ? PER - g : len - done; memcpy(v + done, pattern + g, n); done += n; g = 0; }
        /* 2a. primes < SUB: marked sub-block by sub-block so the bytes stay in L1 */
        size_t nl1 = 0; while (nl1 < nsm && primes[nl1] < SUB) nl1++;
        for (u64 s0 = b0; s0 < bend; s0 += SUB) {
            u64 send = s0 + SUB < bend ? s0 + SUB : bend;
            for (size_t i = 0; i < nl1; i++) {
                u64 p = primes[i], idx = w->nx[i];
                uint8_t inc = (i < nmed) ? 0x11 : 0x10;
                for (; idx < send; idx += p) v[idx - b0] += inc;
                w->nx[i] = idx;
            }
        }
        /* 2b. remaining small-stride primes: adds */
        for (size_t i = nl1; i < nsm; i++) {
            u64 p = primes[i], idx = w->nx[i];
            uint8_t inc = (i < nmed) ? 0x11 : 0x10;
            for (; idx < bend; idx += p) v[idx - b0] += inc;
            w->nx[i] = idx;
        }
        /* 3. bucketed primes: at most one hit per block */
        uint32_t e = w->bhead[bk]; w->bhead[bk] = UINT32_MAX;
        while (e != UINT32_MAX) {
            bent_t *E = &w->be[e]; uint32_t nxt = E->nxt;
            v[E->idx - b0] += (e < nmed) ? 0x11 : 0x10;
            E->idx += E->p;
            if (E->idx < total) { u64 b = E->idx >> BLKLOG; E->nxt = w->bhead[b]; w->bhead[b] = e; }
            e = nxt;
        }
        /* 4. good progressions: subtract */
        for (size_t j = 0; j < na; j++) {
            u64 idx = w->pidx[j];
            if (idx >= bend) continue;
            u64 st = w->pstep[j];
            for (; idx < bend; idx += st) v[idx - b0] -= 1;
            w->pidx[j] = idx;
        }
        /* 5. scan: candidate iff low nibble == 0 and (high nibble != 0 or !primeskip) */
        const __m256i lowm = _mm256_set1_epi8(0x0F), highm = _mm256_set1_epi8((char)0xF0), z = _mm256_setzero_si256();
        for (u64 k0 = 0; k0 < len; k0 += 32) {
            uint32_t mask;
            if (k0 + 32 <= len) {
                __m256i x = _mm256_loadu_si256((const __m256i *)(v + k0));
                uint32_t lz = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_and_si256(x, lowm), z));
                uint32_t hz = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_and_si256(x, highm), z));
                mask = primeskip ? (lz & ~hz) : lz;
            } else {
                mask = 0;
                for (u64 k = k0; k < len; k++) { uint8_t x = v[k]; if (!(x & 0x0F) && ((x & 0xF0) || !primeskip)) mask |= 1u << (k - k0); }
            }
            while (mask) {
                int bpos = __builtin_ctz(mask); mask &= mask - 1;
                u64 m = c0 + 2 * (b0 + k0 + bpos);
                if (m < 5) continue;
                w->cand++;
                if (usefilter && prefilter(m, v[k0 + bpos] >> 4)) continue;
                int nb = 63 - __builtin_clzll(m);
                if (nb != nbcur && nc) { test_batch(cbuf, nc); w->tested += nc; nc = 0; }
                nbcur = nb; cbuf[nc++] = m;
                if (nc == LANES) { test_batch(cbuf, nc); w->tested += nc; nc = 0; }
            }
        }
    }
    if (nc) { test_batch(cbuf, nc); w->tested += nc; }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s lo hi [-t n] [-B b] [-c tA tB] [-noprimeskip] [-list] [-chunk log2] [-ckpt file]\n", argv[0]); return 1; }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int threads = omp_get_max_threads(), chunklog = 28; const char *ckpt = NULL;
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "-t")) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-B")) B = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-c")) { tA = atoll(argv[++i]); tB = atoll(argv[++i]); }
        else if (!strcmp(argv[i], "-noprimeskip")) primeskip = 0;
        else if (!strcmp(argv[i], "-list")) listall = 1;
        else if (!strcmp(argv[i], "-nofilter")) usefilter = 0;
        else if (!strcmp(argv[i], "-chunk")) chunklog = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-ckpt")) ckpt = argv[++i];
    }
    if (hi >= ((u64)1 << 62) || hi <= lo) { fprintf(stderr, "need lo < hi < 2^62\n"); return 1; }
    if (B < 17) B = 17;
    if (!primeskip) usefilter = 0;          /* filter assumes r is not the whole m */
    if (!(lo & 1)) lo++;
    if (!(hi & 1)) hi++;
    omp_set_num_threads(threads);
    double t0 = omp_get_wtime();
    u64 sq = (u64)sqrtl((long double)hi) + 2;
    make_primes(sq > B ? sq : B);
    make_pattern();
    make_fib();
    make_progs();
    double t1 = omp_get_wtime();
    fprintf(stderr, "primes 17..%llu: %zu (medium <= %llu: %zu), good progressions: %zu, setup %.2fs\n",
            (unsigned long long)(sq > B ? sq : B), nprimes, (unsigned long long)B, nmed, nprogs, t1 - t0);

    u64 chunk = (u64)1 << chunklog;
    u64 nchunks = (hi - lo + chunk - 1) / chunk;
    uint8_t *done = calloc(nchunks, 1);
    u64 tot_cand = 0, tot_test = 0, ndone = 0, prefix = 0;
    #pragma omp parallel
    {
        ws_t w; memset(&w, 0, sizeof w);
        w.v = _mm_malloc(BLK + 64, 64);
        w.nx = malloc(nprimes * sizeof(u64));
        w.pidx = malloc((nprogs + 1) * sizeof(u64)); w.pstep = malloc((nprogs + 1) * sizeof(u64));
        w.be = malloc(nprimes * sizeof(bent_t));
        #pragma omp for schedule(dynamic, 1)
        for (i64 c = 0; c < (i64)nchunks; c++) {
            u64 c0 = lo + (u64)c * chunk, c1 = c0 + chunk; if (c1 > hi) c1 = hi;
            do_chunk(c0, c1, &w);
            #pragma omp critical(prog)
            {
                done[c] = 1; ndone++;
                while (prefix < nchunks && done[prefix]) prefix++;
                u64 upto = lo + prefix * chunk; if (upto > hi) upto = hi;
                double el = omp_get_wtime() - t1;
                if (ndone % 32 == 0 || ndone == nchunks) {
                    fprintf(stderr, "[%7.1fs] %llu/%llu chunks, complete below %llu, hits %llu\n", el,
                            (unsigned long long)ndone, (unsigned long long)nchunks, (unsigned long long)upto, (unsigned long long)nhits);
                    if (ckpt) { FILE *f = fopen(ckpt, "w"); if (f) { fprintf(f, "lo=%llu complete_below=%llu hits=%llu elapsed=%.1f\n", (unsigned long long)lo, (unsigned long long)upto, (unsigned long long)nhits, el); fclose(f); } }
                }
            }
        }
        #pragma omp atomic
        tot_cand += w.cand;
        #pragma omp atomic
        tot_test += w.tested;
    }
    double t2 = omp_get_wtime();
    u64 nodd = (hi - lo) / 2;
    printf("range [%llu, %llu): odd m %llu, tested %llu (%.3f%%), hits %llu, time %.2fs (%.3f ns/odd m wall)\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)nodd, (unsigned long long)tot_test,
           100.0 * tot_test / (nodd ? nodd : 1), (unsigned long long)nhits, t2 - t1, 1e9 * (t2 - t1) / (nodd ? nodd : 1));
    (void)listall;
    return 0;
}
