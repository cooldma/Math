// Structured search for counterexamples to Conjecture 1.28 (arXiv 2611.32519):
// odd m >= 5 with F_m in A  <=>  m | F_m + t,  t = 4 if 3|m else 3  (5 does not divide m).
//
// Write m = k*P with P prime, P not dividing k.  By Lemma 2.19, F_{kP} = eps*F_k (mod P), eps = (P/5),
// so P must divide F_k + eps*t.  For each odd k we factor F_k + 3 and F_k - 3 (or +-4 if 3|k) and test
// every prime factor P:  mod P via eps,  mod k via (k*P mod pi(k)) in the good-residue table.
// If both factorizations are complete, *every* m = k*P (P prime, P not dividing k) is excluded.
// Also tests m = k*P^2 directly mod P^2.
//
// usage: kpsearch k0 k1 [-t threads] [-rho iters] [-pm1 B1] [-ecm curves B1]
// build: gcc -O3 -march=native -fopenmp -o kpsearch kpsearch.c -lgmp
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <gmp.h>
#include <omp.h>

typedef unsigned long long u64;
static u64 RHO_ITERS = 200000, PM1_B1 = 200000, ECM_B1 = 50000;
static int ECM_CURVES = 20;
static long TA = 3, TB = 4;   // t for 3 !| m, t for 3 | m  (condition m | F_m + t)
static unsigned *PR; static int NPR;           // primes < 2^20
static const unsigned TRIAL = 1u << 16;

static void sieve(unsigned n) {
    char *c = calloc(n + 1, 1); PR = malloc(sizeof(unsigned) * n / 4 + 64); NPR = 0;
    for (unsigned i = 2; i <= n; i++) if (!c[i]) { PR[NPR++] = i; for (u64 j = (u64)i * i; j <= n; j += i) c[j] = 1; }
    free(c);
}

// F_n mod M (n arbitrary mpz) by fast doubling. res = F_n, res1 = F_{n+1}
static void fibmod(mpz_t res, mpz_t res1, const mpz_t n, const mpz_t M) {
    mpz_t a, b, t1, t2; mpz_inits(a, b, t1, t2, NULL);
    mpz_set_ui(a, 0); mpz_set_ui(b, 1);              // (F_0, F_1)
    for (long i = (long)mpz_sizeinbase(n, 2) - 1; i >= 0; i--) {
        // F_2j = F_j (2F_{j+1} - F_j);  F_2j+1 = F_j^2 + F_{j+1}^2
        mpz_mul_2exp(t1, b, 1); mpz_sub(t1, t1, a); mpz_mul(t1, t1, a); mpz_mod(t1, t1, M);
        mpz_mul(t2, a, a); mpz_addmul(t2, b, b); mpz_mod(t2, t2, M);
        if (mpz_tstbit(n, i)) { mpz_add(a, t1, t2); mpz_mod(a, a, M); mpz_swap(b, a); mpz_swap(a, t2); }
        else { mpz_swap(a, t1); mpz_swap(b, t2); }
    }
    mpz_set(res, a); if (res1) mpz_set(res1, b);
    mpz_clears(a, b, t1, t2, NULL);
}

// ---------- factoring ----------
static int pm1(mpz_t f, const mpz_t N) {
    mpz_t a, g; mpz_inits(a, g, NULL); mpz_set_ui(a, 3); int ok = 0;
    for (int i = 0; i < NPR && PR[i] <= PM1_B1; i++) {
        u64 q = PR[i], qe = q; while (qe * q <= PM1_B1) qe *= q;
        mpz_powm_ui(a, a, qe, N);
        if ((i & 1023) == 1023 || i + 1 == NPR || PR[i + 1] > PM1_B1) {
            mpz_sub_ui(g, a, 1); mpz_gcd(g, g, N);
            if (mpz_cmp_ui(g, 1) > 0) { if (mpz_cmp(g, N) < 0) { mpz_set(f, g); ok = 1; } break; }
        }
    }
    mpz_clears(a, g, NULL); return ok;
}

static int rho(mpz_t f, const mpz_t N, unsigned long c) {
    mpz_t x, y, ys, q, g, t; mpz_inits(x, y, ys, q, g, t, NULL);
    mpz_set_ui(y, 2); mpz_set_ui(q, 1); mpz_set_ui(g, 1); int ok = 0;
    u64 r = 1, it = 0; const u64 m = 256;
    while (mpz_cmp_ui(g, 1) == 0 && it < RHO_ITERS) {
        mpz_set(x, y);
        for (u64 i = 0; i < r; i++) { mpz_mul(y, y, y); mpz_add_ui(y, y, c); mpz_mod(y, y, N); }
        for (u64 k = 0; k < r && mpz_cmp_ui(g, 1) == 0; k += m) {
            mpz_set(ys, y);
            u64 lim = (m < r - k) ? m : r - k;
            for (u64 i = 0; i < lim; i++) {
                mpz_mul(y, y, y); mpz_add_ui(y, y, c); mpz_mod(y, y, N);
                mpz_sub(t, x, y); mpz_mul(q, q, t); mpz_mod(q, q, N);
            }
            it += lim; mpz_gcd(g, q, N);
        }
        r <<= 1;
    }
    if (mpz_cmp(g, N) == 0) {                         // backtrack
        do { mpz_mul(ys, ys, ys); mpz_add_ui(ys, ys, c); mpz_mod(ys, ys, N); mpz_sub(t, x, ys); mpz_gcd(g, t, N); }
        while (mpz_cmp_ui(g, 1) == 0);
    }
    if (mpz_cmp_ui(g, 1) > 0 && mpz_cmp(g, N) < 0) { mpz_set(f, g); ok = 1; }
    mpz_clears(x, y, ys, q, g, t, NULL); return ok;
}

// ECM stage 1, Montgomery curves By^2 = x^3 + A x^2 + x, Suyama parametrisation, x-only ladder.
typedef struct { mpz_t X, Z; } pt;
static void xdbl(pt *R, const pt *P, const mpz_t a24, const mpz_t N, mpz_t u, mpz_t v, mpz_t w) {
    mpz_add(u, P->X, P->Z); mpz_mul(u, u, u); mpz_mod(u, u, N);
    mpz_sub(v, P->X, P->Z); mpz_mul(v, v, v); mpz_mod(v, v, N);
    mpz_mul(R->X, u, v); mpz_mod(R->X, R->X, N);
    mpz_sub(w, u, v); mpz_mul(u, w, a24); mpz_add(u, u, v); mpz_mul(R->Z, w, u); mpz_mod(R->Z, R->Z, N);
}
static void xadd(pt *R, const pt *P, const pt *Q, const pt *D, const mpz_t N, mpz_t u, mpz_t v, mpz_t w) {
    mpz_sub(u, P->X, P->Z); mpz_add(w, Q->X, Q->Z); mpz_mul(u, u, w); mpz_mod(u, u, N);
    mpz_add(v, P->X, P->Z); mpz_sub(w, Q->X, Q->Z); mpz_mul(v, v, w); mpz_mod(v, v, N);
    mpz_add(w, u, v); mpz_mul(w, w, w); mpz_mul(w, w, D->Z);
    mpz_sub(u, u, v); mpz_mul(u, u, u); mpz_mul(u, u, D->X);
    mpz_mod(R->X, w, N); mpz_mod(R->Z, u, N);
}
static void ladder(pt *R, const pt *P, u64 n, const mpz_t a24, const mpz_t N, mpz_t u, mpz_t v, mpz_t w, pt *T0, pt *T1) {
    mpz_set(T0->X, P->X); mpz_set(T0->Z, P->Z); xdbl(T1, P, a24, N, u, v, w);
    for (int i = 62 - __builtin_clzll(n); i >= 0; i--) {
        if ((n >> i) & 1) { xadd(T0, T1, T0, P, N, u, v, w); xdbl(T1, T1, a24, N, u, v, w); }
        else { xadd(T1, T0, T1, P, N, u, v, w); xdbl(T0, T0, a24, N, u, v, w); }
    }
    mpz_set(R->X, T0->X); mpz_set(R->Z, T0->Z);
}
static int ecm(mpz_t f, const mpz_t N, unsigned long sigma) {
    mpz_t u, v, w, a24, t, s; pt P, T0, T1; int ok = 0;
    mpz_inits(u, v, w, a24, t, s, P.X, P.Z, T0.X, T0.Z, T1.X, T1.Z, NULL);
    // u = sigma^2 - 5, v = 4 sigma, X = u^3, Z = v^3, A+2 = (v-u)^3 (3u+v) / (4 u^3 v)
    mpz_set_ui(s, sigma); mpz_mul(u, s, s); mpz_sub_ui(u, u, 5); mpz_mul_ui(v, s, 4);
    mpz_powm_ui(P.X, u, 3, N); mpz_powm_ui(P.Z, v, 3, N);
    mpz_sub(t, v, u); mpz_powm_ui(t, t, 3, N); mpz_mul_ui(w, u, 3); mpz_add(w, w, v); mpz_mul(t, t, w); mpz_mod(t, t, N);
    mpz_mul_ui(w, P.X, 16); mpz_mul(w, w, v); mpz_mod(w, w, N);      // a24 = (A+2)/4 = t / (16 u^3 v)
    if (!mpz_invert(s, w, N)) { mpz_gcd(s, w, N); if (mpz_cmp_ui(s, 1) > 0 && mpz_cmp(s, N) < 0) { mpz_set(f, s); ok = 1; } goto done; }
    mpz_mul(a24, t, s); mpz_mod(a24, a24, N);
    for (int i = 0; i < NPR && PR[i] <= ECM_B1; i++) {
        u64 q = PR[i], qe = q; while (qe * q <= ECM_B1) qe *= q;
        ladder(&P, &P, qe, a24, N, u, v, w, &T0, &T1);
    }
    mpz_gcd(s, P.Z, N);
    if (mpz_cmp_ui(s, 1) > 0 && mpz_cmp(s, N) < 0) { mpz_set(f, s); ok = 1; }
done:
    mpz_clears(u, v, w, a24, t, s, P.X, P.Z, T0.X, T0.Z, T1.X, T1.Z, NULL); return ok;
}

// factor |N| into primes (appended to out[]); returns 1 if complete
#define MAXF 256
static int factor(const mpz_t N0, mpz_t *out, int *nout) {
    mpz_t N, stk[MAXF], f; int ns = 0, complete = 1; mpz_init(N); mpz_init(f); mpz_abs(N, N0);
    *nout = 0;
    if (mpz_cmp_ui(N, 1) <= 0) { mpz_clears(N, f, NULL); return mpz_sgn(N0) != 0; }
    for (int i = 0; i < NPR && PR[i] < TRIAL; i++)
        if (mpz_divisible_ui_p(N, PR[i])) { mpz_set_ui(out[(*nout)++], PR[i]); do mpz_divexact_ui(N, N, PR[i]); while (mpz_divisible_ui_p(N, PR[i])); }
    if (mpz_cmp_ui(N, 1) > 0) { mpz_init_set(stk[ns++], N); }
    while (ns > 0) {
        mpz_t cur; mpz_t *c = &cur; ns--; mpz_init_set(cur, stk[ns]); mpz_clear(stk[ns]);
        if (mpz_probab_prime_p(*c, 25)) { mpz_set(out[(*nout)++], *c); mpz_clear(*c); continue; }
        if (mpz_perfect_power_p(*c)) {                     // rare; handle squares
            mpz_t r; mpz_init(r);
            for (unsigned e = 2; e < 64; e++) if (mpz_root(r, *c, e)) { mpz_set(f, r); break; }
            mpz_clear(r);
        } else {
            int found = pm1(f, *c);
            for (unsigned long cc = 1; !found && cc <= 2; cc++) found = rho(f, *c, cc);
            for (int e = 0; !found && e < ECM_CURVES; e++) found = ecm(f, *c, 6 + e * 7919 + mpz_fdiv_ui(*c, 1000003));
            if (!found) { complete = 0; mpz_clear(*c); continue; }
        }
        if (ns + 2 > MAXF || *nout + 2 > MAXF) { complete = 0; mpz_clear(*c); continue; }
        mpz_init(stk[ns]); mpz_divexact(stk[ns], *c, f); ns++;
        mpz_init_set(stk[ns], f); ns++;
        mpz_clear(*c);
    }
    // dedupe (perfect-power splits may repeat primes)
    int w = 0;
    for (int i = 0; i < *nout; i++) { int dup = 0; for (int j = 0; j < w; j++) if (!mpz_cmp(out[i], out[j])) { dup = 1; break; } if (!dup) mpz_swap(out[w++], out[i]); }
    *nout = w;
    mpz_clears(N, f, NULL); return complete;
}

// ---------- main search ----------
static u64 hits = 0, tested = 0, kcomplete = 0, knum = 0;

static int check_def(const mpz_t m) {     // returns bit0: m | F_m + t (direct);  bit1: F_m in A (via F_m mod 4m)
    mpz_t n, r; mpz_inits(n, r, NULL); int ok = 0;
    long t = mpz_divisible_ui_p(m, 3) ? TB : TA;
    mpz_set(n, m); fibmod(r, NULL, n, m); if (t >= 0) mpz_add_ui(r, r, t); else mpz_sub_ui(r, r, -t); mpz_mod(r, r, m);
    if (mpz_sgn(r) == 0) ok |= 1;
    // bit1: F_m itself lies in A  <=>  (F_m + 2) mod 4m in {1, 2, 2m-2, 4m-1}   (Lemma 2.18(2), m odd)
    { mpz_t M4, q; mpz_inits(M4, q, NULL); mpz_mul_ui(M4, m, 4); mpz_set(n, m); fibmod(r, NULL, n, M4);
      mpz_add_ui(r, r, 2); mpz_mod(r, r, M4);
      mpz_mul_ui(q, m, 2); mpz_sub_ui(q, q, 2); int in = !mpz_cmp_ui(r, 1) || !mpz_cmp_ui(r, 2) || !mpz_cmp(r, q);
      mpz_sub_ui(q, M4, 1); in |= !mpz_cmp(r, q); if (in) ok |= 2; mpz_clears(M4, q, NULL); }
    mpz_clears(n, r, NULL); return ok;
}

static void do_k(u64 k) {
    // Pisano period and good residues for t = 3 and t = 4
    u64 a = 0, b = 1, pi = 0;
    unsigned char *good = NULL; size_t cap = 0;
    do {
        if (pi >= cap) { cap = cap ? cap * 2 : 1024; good = realloc(good, cap); }
        long long ra = (long long)(a % k);
        good[pi] = (unsigned char)((((ra + TA) % (long long)k + (long long)k) % (long long)k == 0) | (((((ra + TB) % (long long)k + (long long)k) % (long long)k) == 0) << 1));
        u64 c = (a + b) % k; a = b; b = c; pi++;
    } while (!(a == 0 && b == 1));
    long t = (k % 3 == 0) ? TB : TA; int tb = (k % 3 == 0);
    mpz_t Fk, N, fac[MAXF], m, mm, r, P2, idx; int nf, complete = 1;
    mpz_inits(Fk, N, m, mm, r, P2, idx, NULL); for (int i = 0; i < MAXF; i++) mpz_init(fac[i]);
    mpz_fib_ui(Fk, k);
    char line[4096]; int lp = 0;
    lp += snprintf(line + lp, sizeof line - lp, "k %llu", k);
    for (int s = -1; s <= 1; s += 2) {
        // P | F_k + s*t with eps(P) = s;  P = 3 (only when 3 does not divide k) uses t = 4 -- tested separately below
        mpz_set(N, Fk); { long st = s * t; if (st >= 0) mpz_add_ui(N, N, st); else mpz_sub_ui(N, N, -st); }
        if (mpz_sgn(N) == 0) {                     // degenerate: every prime P with eps = s works mod P (cannot occur for t = 3, 4)
            #pragma omp critical
            { fprintf(stderr, "DEGENERATE k=%llu s=%d: F_k + s*t = 0, every m = k*P with (P/5) = s needs only the mod-k test\n", k, s); }
            complete = 0; continue;
        }
        int c = factor(N, fac, &nf); complete &= c;
        size_t maxd = 0;
        for (int i = 0; i < nf; i++) {
            size_t d = mpz_sizeinbase(fac[i], 10); if (d > maxd) maxd = d;
            if (mpz_cmp_ui(fac[i], 5) <= 0) continue;                    // P = 2,3,5 handled separately
            if (mpz_fits_ulong_p(fac[i]) && k % mpz_get_ui(fac[i]) == 0) continue;
            unsigned p5 = mpz_fdiv_ui(fac[i], 5); int eps = (p5 == 1 || p5 == 4) ? 1 : -1;
            // a = 1
            if (eps == s) {
                unsigned long rr = mpz_fdiv_ui(fac[i], pi);                // P mod pi(k)
                u64 idx1 = (u64)((unsigned __int128)(k % pi) * rr % pi);
                __atomic_fetch_add(&tested, 1, __ATOMIC_RELAXED);
                if (good[idx1] & (tb ? 2 : 1)) {
                    mpz_mul_ui(m, fac[i], k);
                    int def = check_def(m);
                    #pragma omp critical
                    { gmp_printf("HIT k=%llu P=%Zd (a=1) def=%d digits=%zu\n", k, fac[i], def, mpz_sizeinbase(m, 10)); fflush(stdout); }
                    __atomic_fetch_add(&hits, 1, __ATOMIC_RELAXED);
                }
            }
            // a = 2: need F_{kP^2} = -t mod P^2 (mod P this is F_k = -t, i.e. s = +1)
            if (s == 1 && mpz_sizeinbase(fac[i], 2) <= 4000) {
                unsigned long rr = mpz_fdiv_ui(fac[i], pi);
                u64 idx2 = (u64)((unsigned __int128)((unsigned __int128)(k % pi) * rr % pi) * rr % pi);
                if (good[idx2] & (tb ? 2 : 1)) {
                    mpz_mul(P2, fac[i], fac[i]); mpz_mul_ui(idx, P2, k); fibmod(r, NULL, idx, P2);
                    if (t >= 0) mpz_add_ui(r, r, t); else mpz_sub_ui(r, r, -t); mpz_mod(r, r, P2);
                    if (mpz_sgn(r) == 0) {
                        mpz_mul_ui(m, P2, k); int def = check_def(m);
                        #pragma omp critical
                        { gmp_printf("HIT k=%llu P=%Zd (a=2) def=%d\n", k, fac[i], def); fflush(stdout); }
                        __atomic_fetch_add(&hits, 1, __ATOMIC_RELAXED);
                    }
                }
            }
        }
        lp += snprintf(line + lp, sizeof line - lp, " | %c: %d primes, max %zu digits%s", s > 0 ? '+' : '-', nf, maxd, c ? "" : " INCOMPLETE");
    }
    // P = 3 when 3 does not divide k: m = 3k, t = 4 -- just test directly; also P = 3^2.
    if (k % 3) for (int e = 1; e <= 2; e++) { mpz_set_ui(m, k); mpz_mul_ui(m, m, e == 1 ? 3 : 9);
        mpz_add_ui(idx, m, 0); fibmod(r, NULL, idx, m); if (TB >= 0) mpz_add_ui(r, r, TB); else mpz_sub_ui(r, r, -TB); mpz_mod(r, r, m);
        if (mpz_sgn(r) == 0) {
            #pragma omp critical
            { printf("HIT k=%llu P=3 e=%d def=%d\n", k, e, check_def(m)); fflush(stdout); }
        }
    }
    __atomic_fetch_add(&knum, 1, __ATOMIC_RELAXED);
    if (complete) __atomic_fetch_add(&kcomplete, 1, __ATOMIC_RELAXED);
    #pragma omp critical
    { fprintf(stderr, "%s%s\n", line, complete ? " | COMPLETE" : ""); }
    free(good);
    mpz_clears(Fk, N, m, mm, r, P2, idx, NULL); for (int i = 0; i < MAXF; i++) mpz_clear(fac[i]);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s k0 k1 [-t n] [-rho iters] [-pm1 B1] [-ecm curves B1]\n", argv[0]); return 1; }
    u64 k0 = strtoull(argv[1], 0, 10), k1 = strtoull(argv[2], 0, 10); int th = omp_get_max_threads();
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "-t")) th = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-c")) { TA = atol(argv[++i]); TB = atol(argv[++i]); }
        else if (!strcmp(argv[i], "-rho")) RHO_ITERS = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-pm1")) PM1_B1 = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-ecm")) { ECM_CURVES = atoi(argv[++i]); ECM_B1 = strtoull(argv[++i], 0, 10); }
    }
    sieve(1u << 22);
    if (k0 < 3) k0 = 3;
    double t0 = omp_get_wtime();
    #pragma omp parallel for schedule(dynamic, 1) num_threads(th)
    for (long long kk = (long long)k1; kk >= (long long)k0; kk--) {      // large k first for load balance
        u64 k = (u64)kk; if (!(k & 1) || k % 5 == 0) continue;
        do_k(k);
    }
    fprintf(stderr, "done k in [%llu,%llu]: %llu k values, %llu fully factored, %llu (k,P) pairs tested, %llu hits, %.1fs\n",
            k0, k1, knum, kcomplete, tested, hits, omp_get_wtime() - t0);
    printf("SUMMARY k0=%llu k1=%llu kvals=%llu complete=%llu pairs=%llu hits=%llu\n", k0, k1, knum, kcomplete, tested, hits);
    return 0;
}
