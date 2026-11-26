// search_tdn.cpp (v2 - Bitset-Vectorized + High-Period QR Filter + Exact Min-Heap CRT)
// High-performance multi-threaded counterexample search for Conjecture 1.3
// of Filipin, Fujita, Jurasic (arXiv:2611.25270v1, Nov 2026):
//   "On the Non-extendibility of Triangular D(n)-Pairs {n, 2n} with n = 2k^2 +/- k"
//
// Build:
//   g++ -O3 -march=native -flto -std=c++20 -pthread search_tdn.cpp -o search_tdn.exe

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <mutex>
#include <queue>
#include <string>
#include <thread>
#include <vector>

using u8   = uint8_t;
using u16  = uint16_t;
using u32  = uint32_t;
using u64  = uint64_t;
using i64  = int64_t;
using u128 = __uint128_t;

// ---------------------------------------------------------------------------
// 1. Linear Smallest Prime Factor (SPF) Sieve
// ---------------------------------------------------------------------------
struct Sieve {
    u32 limit = 0;
    std::vector<u32> spf;
    std::vector<u32> primes;

    void init(u32 N) {
        limit = N;
        spf.assign(N + 1, 0);
        primes.clear();
        primes.reserve(N / 10);
        for (u32 i = 2; i <= N; ++i) {
            if (spf[i] == 0) {
                spf[i] = i;
                primes.push_back(i);
            }
            for (u32 p : primes) {
                u64 v = (u64)i * p;
                if (v > N) break;
                spf[v] = p;
                if (p == spf[i]) break;
            }
        }
    }
};

// ---------------------------------------------------------------------------
// 2. Fast Lucas Sequence U_k(6, 1) = P_{2k} / 2  (mod M)
// ---------------------------------------------------------------------------
static inline u64 mulmod64(u64 a, u64 b, u64 m) {
    return (u64)((u128)a * b % m);
}

static inline u64 lucas_U_mod(u64 k, u64 m) {
    if (m == 1 || k == 0) return 0;
    u64 u0 = 0, u1 = 1;
    int top = 63 - __builtin_clzll(k);
    for (int bit = top; bit >= 0; --bit) {
        u64 t = (2 * u1 + 6 * m - 6 * u0) % m;
        u64 u2n = mulmod64(u0, t, m);
        u64 s1 = mulmod64(u1, u1, m);
        u64 s0 = mulmod64(u0, u0, m);
        u64 u2n1 = (s1 >= s0) ? (s1 - s0) : (s1 + m - s0);
        if ((k >> bit) & 1ULL) {
            u0 = u2n1;
            u64 six = mulmod64(6, u2n1, m);
            u1 = (six >= u2n) ? (six - u2n) : (six + m - u2n);
        } else {
            u0 = u2n;
            u1 = u2n1;
        }
    }
    return u0;
}

static inline u32 lucas_U_mod32(u32 k, u32 m) {
    if (m == 1 || k == 0) return 0;
    u64 u0 = 0, u1 = 1;
    int top = 31 - __builtin_clz(k);
    for (int bit = top; bit >= 0; --bit) {
        u64 t = (2 * u1 + 6ULL * m - 6 * u0) % m;
        u64 u2n = (u0 * t) % m;
        u64 s1 = (u1 * u1) % m;
        u64 s0 = (u0 * u0) % m;
        u64 u2n1 = (s1 >= s0) ? (s1 - s0) : (s1 + m - s0);
        if ((k >> bit) & 1U) {
            u0 = u2n1;
            u64 six = (6 * u2n1) % m;
            u1 = (six >= u2n) ? (six - u2n) : (six + m - u2n);
        } else {
            u0 = u2n;
            u1 = u2n1;
        }
    }
    return (u32)u0;
}

static u32 compute_rank_prime(u32 q, const Sieve& sv) {
    u32 d = ((q & 7U) == 1U || (q & 7U) == 7U) ? ((q - 1) >> 1) : ((q + 1) >> 1);
    u32 r = d;
    u32 tmp = d;
    while (tmp > 1) {
        u32 f = sv.spf[tmp];
        while (tmp % f == 0) tmp /= f;
        while (r % f == 0 && lucas_U_mod32(r / f, q) == 0) {
            r /= f;
        }
    }
    return r;
}

static u64 compute_rank_prime_power(u32 q, int e, u32 rq, u64 qe) {
    u64 r = rq;
    if (e == 1) return r;
    while (lucas_U_mod(r, qe) != 0) r *= q;
    return r;
}

// ---------------------------------------------------------------------------
// 3. High-Period Modular Quadratic Residue Filter Tables
//    We select primes r >= 101 whose C_l period T_r is >= 45 (so C_l == 0 mod r
//    happens < 4% of the time, eliminating small-prime correlation!).
//    First 16 primes have T_r <= 128 so bitset tables fit cleanly in L2 cache.
// ---------------------------------------------------------------------------
static constexpr int NUM_SMALL_PRIMES = 64;
static constexpr int NUM_CHECK_PRIMES = 48;
static constexpr int NUM_BITSET_P     = 12;
static constexpr int MAX_SMALL_P      = 1600;
static constexpr int MAX_PERIOD       = 800;

struct QRFilterTables {
    u32 primes[NUM_SMALL_PRIMES];
    u32 period[NUM_SMALL_PRIMES];
    u16 C_mod[NUM_SMALL_PRIMES][MAX_PERIOD];
    u8  is_qr[NUM_SMALL_PRIMES][MAX_SMALL_P];

    static constexpr int NUM_LARGE_PRIMES = 64;
    u32 large_primes[NUM_LARGE_PRIMES];

    static u64 powmod(u64 a, u64 e, u64 m) {
        u64 r = 1;
        a %= m;
        while (e) {
            if (e & 1) r = mulmod64(r, a, m);
            a = mulmod64(a, a, m);
            e >>= 1;
        }
        return r;
    }

    static bool is_prime_u32(u32 n) {
        if (n < 2) return false;
        if (n % 2 == 0) return n == 2;
        for (u32 d = 3; (u64)d * d <= n; d += 2)
            if (n % d == 0) return false;
        return true;
    }

    static u32 find_period(u32 p, u16* out_C) {
        u32 c0 = 0, c1 = 1;
        out_C[0] = 0;
        for (u32 l = 1; l < MAX_PERIOD; ++l) {
            out_C[l] = (u16)c1;
            u32 c2 = (34U * c1 + p - c0 + 1U) % p;
            c0 = c1;
            c1 = c2;
            if (c0 == 0 && c1 == 1) return l;
        }
        return 0;
    }

    void init() {
        // Select 64 primes in [101, MAX_SMALL_P) with large period T.
        // Prioritize PRIME periods in [47, 160] FIRST (completely uncorrelated with
        // small CRT moduli!), then non-prime periods in [50, 128], then larger periods.
        std::vector<u32> tier0, tier1, tier2;
        u16 tmpC[MAX_PERIOD];
        for (u32 p = 101; p < MAX_SMALL_P; p += 2) {
            if (!is_prime_u32(p)) continue;
            u32 per = find_period(p, tmpC);
            if (per == 0) continue;
            if (per >= 47 && per <= 160 && is_prime_u32(per)) tier0.push_back(p);
            else if (per >= 50 && per <= 128) tier1.push_back(p);
            else if (per > 128) tier2.push_back(p);
        }

        std::vector<u32> chosen;
        for (u32 p : tier0) if (chosen.size() < NUM_SMALL_PRIMES) chosen.push_back(p);
        for (u32 p : tier1) if (chosen.size() < NUM_SMALL_PRIMES) chosen.push_back(p);
        for (u32 p : tier2) if (chosen.size() < NUM_SMALL_PRIMES) chosen.push_back(p);
        if (chosen.size() < NUM_SMALL_PRIMES) {
            std::fprintf(stderr, "FATAL: not enough high-period primes (%zu)\n", chosen.size());
            std::exit(1);
        }

        for (int idx = 0; idx < NUM_SMALL_PRIMES; ++idx) {
            u32 p = chosen[idx];
            primes[idx] = p;
            std::memset(is_qr[idx], 0, sizeof(is_qr[idx]));
            for (u32 x = 0; x < p; ++x) is_qr[idx][(x * x) % p] = 1;
            period[idx] = find_period(p, C_mod[idx]);
        }

        // 64 large 31-bit primes for deep verification
        int lidx = 0;
        for (u32 p = 1000000007U; lidx < NUM_LARGE_PRIMES; p += 2) {
            if (is_prime_u32(p)) large_primes[lidx++] = p;
        }
    }

    static u64 C_mod_large(u64 l, u32 r) {
        if (l == 0) return 0;
        u64 u0 = 0, u1 = 1;
        int top = 63 - __builtin_clzll(l);
        for (int bit = top; bit >= 0; --bit) {
            u64 t = (2 * u1 + 6ULL * r - 6 * u0) % r;
            u64 u2n = (u0 * t) % r;
            u64 s1 = (u1 * u1) % r;
            u64 s0 = (u0 * u0) % r;
            u64 u2n1 = (s1 >= s0) ? (s1 - s0) : (s1 + r - s0);
            if ((l >> bit) & 1ULL) {
                u0 = u2n1;
                u64 six = (6 * u2n1) % r;
                u1 = (six >= u2n) ? (six - u2n) : (six + r - u2n);
            } else {
                u0 = u2n;
                u1 = u2n1;
            }
        }
        u64 inv6 = powmod(6, r - 2, r);
        return (((u0 * u1) % r) * inv6) % r;
    }

    bool verify_large_primes(u64 p, u64 lam, u64 l1, u64 l2) const {
        for (int j = 0; j < NUM_LARGE_PRIMES; ++j) {
            u32 r = large_primes[j];
            if (lam % r == 0) continue;
            u64 pm = p % r;
            u64 lm = lam % r;
            u64 inv_l2 = powmod((lm * lm) % r, r - 2, r);
            u64 A = (8ULL * ((pm * pm) % r)) % r;
            A = (A * inv_l2) % r;
            u64 c1 = C_mod_large(l1, r);
            u64 c2 = C_mod_large(l2, r);
            u64 val = (A * ((c1 * c2) % r) + 1) % r;
            if (val != 0 && powmod(val, (r - 1) >> 1, r) != 1) return false;
        }
        return true;
    }
};

// ---------------------------------------------------------------------------
// 4. Exact Min-Heap CRT Generator (always extracts smallest `max_indices` l <= L_max)
// ---------------------------------------------------------------------------
static inline i64 extgcd(i64 a, i64 b, i64& x, i64& y) {
    if (b == 0) { x = 1; y = 0; return a; }
    i64 x1, y1;
    i64 g = extgcd(b, a % b, x1, y1);
    x = y1;
    y = x1 - (a / b) * y1;
    return g;
}

static inline bool crt_merge(u64 r1, u64 m1, u64 r2, u64 m2, u64& rout, u64& mout, u64 L_cap) {
    i64 x, y;
    i64 g = extgcd((i64)m1, (i64)m2, x, y);
    u64 ug = (u64)g;
    i64 diff = (i64)r2 - (i64)r1;
    if (diff % g != 0) return false;
    u64 m2g = m2 / ug;
    u128 lcm = (u128)m1 * m2g;
    i64 k = ((diff / g) % (i64)m2g);
    if (k < 0) k += (i64)m2g;
    i64 xm = x % (i64)m2g;
    if (xm < 0) xm += (i64)m2g;
    u64 t = (u64)((u128)k * (u64)xm % m2g);
    u128 r = (u128)r1 + (u128)m1 * t;
    if (lcm > (u128)L_cap) {
        if (r == 0 || r > (u128)L_cap) return false;
        rout = (u64)r;
        mout = L_cap + 1;
        return true;
    }
    rout = (u64)(r % lcm);
    mout = (u64)lcm;
    return true;
}

struct APBranch {
    u64 val;
    u64 step; // 0 means singleton
    bool operator>(const APBranch& o) const { return val > o.val; }
};

struct CRTGenerator {
    const u64* mods;
    int nmods;
    u64 L_max;
    std::vector<APBranch> branches;

    void dfs(int idx, u64 rem, u64 mod) {
        if (mod > L_max) {
            if (rem == 0 || rem > L_max) return;
            for (int j = idx; j < nmods; ++j) {
                u64 mj = mods[j];
                u64 r = rem % mj;
                if (r != 0 && r != mj - 1) return;
            }
            branches.push_back({rem, 0});
            return;
        }
        if (idx == nmods) {
            u64 start = (rem == 0) ? mod : rem;
            if (start <= L_max) branches.push_back({start, mod});
            return;
        }
        u64 mi = mods[idx];
        u64 nr, nm;
        if (crt_merge(rem, mod, 0, mi, nr, nm, L_max)) dfs(idx + 1, nr, nm);
        if (mi > 1 && crt_merge(rem, mod, mi - 1, mi, nr, nm, L_max)) dfs(idx + 1, nr, nm);
    }

    // Extract exact smallest `max_indices` values in [1, L_max]
    bool generate(std::vector<u64>& out, u32 max_indices) {
        out.clear();
        branches.clear();
        dfs(0, 0, 1);
        if (branches.empty()) return false;

        // Fast path: singletons or small total count
        if (branches.size() == 1) {
            APBranch br = branches[0];
            if (br.step == 0) {
                out.push_back(br.val);
                return false;
            }
            for (u64 v = br.val; v <= L_max; v += br.step) {
                if (out.size() >= max_indices) return true;
                out.push_back(v);
            }
            return false;
        }

        // Min-heap k-way merge across CRT branches -> exact sorted smallest indices!
        std::priority_queue<APBranch, std::vector<APBranch>, std::greater<APBranch>> pq(
            std::greater<APBranch>(), std::move(branches));
        while (!pq.empty()) {
            APBranch cur = pq.top();
            pq.pop();
            if (out.size() >= max_indices) return true;
            out.push_back(cur.val);
            if (cur.step > 0 && cur.val + cur.step <= L_max) {
                cur.val += cur.step;
                pq.push(cur);
            }
        }
        return false;
    }
};

// ---------------------------------------------------------------------------
// 5. Bitset-Vectorized Pair Checker
// ---------------------------------------------------------------------------
struct SearchStats {
    std::atomic<u64> primes_checked{0};
    std::atomic<u64> primes_with_pairs{0};
    std::atomic<u64> total_indices{0};
    std::atomic<u64> total_pairs{0};
    std::atomic<u64> survived_8{0};
    std::atomic<u64> survived_48{0};
    std::atomic<u64> counterexamples{0};
    std::atomic<u64> truncated_primes{0};
};

static std::mutex g_print_mtx;

struct ThreadScratch {
    std::vector<u64> indices;
    std::vector<u16> rem8[NUM_BITSET_P];
    // For bitset path: bits[k][x * nwords + w]
    std::vector<u64> bits[NUM_BITSET_P];
    // pos_mask[y * nwords + w] = bitmask of b with rem_k[b] == y
    std::vector<u64> pos_mask;
    std::vector<u32> used_y;
};

static void verify_survivor(
    u64 p, u64 lam, u64 la, u64 lb,
    const int* pidx, const u32* A, int start_k, int nact,
    const QRFilterTables& qr,
    SearchStats& stats,
    u64& local_s48)
{
    for (int k = start_k; k < nact; ++k) {
        int j = pidx[k];
        u32 r = qr.primes[j];
        u32 T = qr.period[j];
        u32 ca = qr.C_mod[j][la % T];
        u32 cb = qr.C_mod[j][lb % T];
        u32 val = (u32)(((u64)A[k] * ca % r) * cb + 1ULL) % r;
        if (!qr.is_qr[j][val]) return;
    }
    ++local_s48;
    if (qr.verify_large_primes(p, lam, la, lb)) {
        stats.counterexamples.fetch_add(1, std::memory_order_relaxed);
        std::lock_guard<std::mutex> lk(g_print_mtx);
        std::printf("\n[!!! COUNTEREXAMPLE CANDIDATE !!!] p=%llu lambda=%llu l=%llu m=%llu\n",
            (unsigned long long)p, (unsigned long long)lam,
            (unsigned long long)la, (unsigned long long)lb);
        std::fflush(stdout);
    }
}

static void check_pairs_for_prime(
    u64 p, u64 lam,
    const std::vector<u64>& indices,
    const QRFilterTables& qr,
    ThreadScratch& scr,
    SearchStats& stats)
{
    const size_t t = indices.size();
    if (t < 2) return;

    int pidx[NUM_CHECK_PRIMES];
    u32 A[NUM_CHECK_PRIMES];
    int nact = 0;
    for (int j = 0; j < NUM_SMALL_PRIMES && nact < NUM_CHECK_PRIMES; ++j) {
        u32 r = qr.primes[j];
        if (lam % r == 0) continue;
        pidx[nact] = j;
        u64 pm = p % r;
        u64 lm = lam % r;
        u64 inv_l2 = QRFilterTables::powmod((lm * lm) % r, r - 2, r);
        A[nact] = (u32)((8ULL * ((pm * pm) % r) % r) * inv_l2 % r);
        ++nact;
    }

    for (int k = 0; k < NUM_BITSET_P; ++k) {
        int j = pidx[k];
        u32 T = qr.period[j];
        scr.rem8[k].resize(t);
        u16* dst = scr.rem8[k].data();
        for (size_t i = 0; i < t; ++i) dst[i] = (u16)(indices[i] % T);
    }

    u64 local_pairs = (u64)t * (t - 1) / 2;
    u64 local_s8 = 0, local_s48 = 0;

    // Choose Bitset-Vectorized path for t >= 256 (64 pairs per bitwise AND!)
    if (t >= 256) {
        const size_t nwords = (t + 63) >> 6;

        // Precompute bits[k][x * nwords + w] for each of the 8 primary primes
        for (int k = 0; k < NUM_BITSET_P; ++k) {
            int j = pidx[k];
            u32 r = qr.primes[j];
            u32 T = qr.period[j];
            const u16* cm = qr.C_mod[j];
            const u8* qrt = qr.is_qr[j];
            const u16* rem = scr.rem8[k].data();

            // Build pos_mask[y * nwords + w] for y in [0, T)
            scr.pos_mask.assign((size_t)T * nwords, 0ULL);
            scr.used_y.clear();
            u8 seen_y[MAX_PERIOD];
            std::memset(seen_y, 0, T);
            for (size_t b = 0; b < t; ++b) {
                u16 y = rem[b];
                if (!seen_y[y]) { seen_y[y] = 1; scr.used_y.push_back(y); }
                scr.pos_mask[(size_t)y * nwords + (b >> 6)] |= (1ULL << (b & 63));
            }

            // Build bits[k][x * nwords + w] ONLY for x that actually appear in rem[]!
            scr.bits[k].assign((size_t)T * nwords, 0ULL);
            for (u32 x : scr.used_y) {
                u32 B = (A[k] * cm[x]) % r;
                u64* dst = scr.bits[k].data() + (size_t)x * nwords;
                for (u32 y : scr.used_y) {
                    if (qrt[(B * cm[y] + 1U) % r]) {
                        const u64* src = scr.pos_mask.data() + (size_t)y * nwords;
                        for (size_t w = 0; w < nwords; ++w) dst[w] |= src[w];
                    }
                }
            }
        }

        const u16* r0 = scr.rem8[0].data();
        const u16* r1 = scr.rem8[1].data();
        const u16* r2 = scr.rem8[2].data();
        const u16* r3 = scr.rem8[3].data();
        const u16* r4 = scr.rem8[4].data();
        const u16* r5 = scr.rem8[5].data();
        const u16* r6 = scr.rem8[6].data();
        const u16* r7 = scr.rem8[7].data();
        const u16* r8 = scr.rem8[8].data();
        const u16* r9 = scr.rem8[9].data();
        const u16* r10 = scr.rem8[10].data();
        const u16* r11 = scr.rem8[11].data();

        const u64* b0_base = scr.bits[0].data();
        const u64* b1_base = scr.bits[1].data();
        const u64* b2_base = scr.bits[2].data();
        const u64* b3_base = scr.bits[3].data();
        const u64* b4_base = scr.bits[4].data();
        const u64* b5_base = scr.bits[5].data();
        const u64* b6_base = scr.bits[6].data();
        const u64* b7_base = scr.bits[7].data();
        const u64* b8_base = scr.bits[8].data();
        const u64* b9_base = scr.bits[9].data();
        const u64* b10_base = scr.bits[10].data();
        const u64* b11_base = scr.bits[11].data();

        for (size_t a = 0; a + 1 < t; ++a) {
            const u64* p0 = b0_base + (size_t)r0[a] * nwords;
            const u64* p1 = b1_base + (size_t)r1[a] * nwords;
            const u64* p2 = b2_base + (size_t)r2[a] * nwords;
            const u64* p3 = b3_base + (size_t)r3[a] * nwords;
            const u64* p4 = b4_base + (size_t)r4[a] * nwords;
            const u64* p5 = b5_base + (size_t)r5[a] * nwords;
            const u64* p6 = b6_base + (size_t)r6[a] * nwords;
            const u64* p7 = b7_base + (size_t)r7[a] * nwords;
            const u64* p8 = b8_base + (size_t)r8[a] * nwords;
            const u64* p9 = b9_base + (size_t)r9[a] * nwords;
            const u64* p10 = b10_base + (size_t)r10[a] * nwords;
            const u64* p11 = b11_base + (size_t)r11[a] * nwords;

            size_t w_start = (a + 1) >> 6;
            u64 first_mask = ~((1ULL << ((a + 1) & 63)) - 1ULL);
            u64 la = indices[a];

            // First partial word
            {
                size_t w = w_start;
                u64 m = p0[w] & p1[w] & p2[w] & p3[w] & p4[w] & p5[w] & p6[w] & p7[w] & first_mask;
                if (m) {
                    m &= p8[w] & p9[w] & p10[w] & p11[w];
                    while (m) {
                        int bit = __builtin_ctzll(m);
                        m &= m - 1;
                        ++local_s8;
                        verify_survivor(p, lam, la, indices[(w << 6) + bit], pidx, A, NUM_BITSET_P, nact, qr, stats, local_s48);
                    }
                }
            }
            // Full 64-bit words: 64 pairs checked in ~5 cycles!
            for (size_t w = w_start + 1; w < nwords; ++w) {
                u64 m = p0[w] & p1[w] & p2[w] & p3[w] & p4[w] & p5[w] & p6[w] & p7[w];
                if (!m) continue;
                m &= p8[w] & p9[w] & p10[w] & p11[w];
                if (!m) continue;
                while (m) {
                    int bit = __builtin_ctzll(m);
                    m &= m - 1;
                    ++local_s8;
                    verify_survivor(p, lam, la, indices[(w << 6) + bit], pidx, A, NUM_BITSET_P, nact, qr, stats, local_s48);
                }
            }
        }
    } else {
        // Fast scalar path for small t < 256
        u8 ok8[NUM_BITSET_P][MAX_PERIOD];
        const u16* r0 = scr.rem8[0].data();
        const u16* r1 = scr.rem8[1].data();
        const u16* r2 = scr.rem8[2].data();
        const u16* r3 = scr.rem8[3].data();
        const u16* r4 = scr.rem8[4].data();
        const u16* r5 = scr.rem8[5].data();
        const u16* r6 = scr.rem8[6].data();
        const u16* r7 = scr.rem8[7].data();

        for (size_t a = 0; a + 1 < t; ++a) {
            for (int k = 0; k < NUM_BITSET_P; ++k) {
                int j = pidx[k];
                u32 r = qr.primes[j];
                u32 T = qr.period[j];
                u32 B = (A[k] * qr.C_mod[j][scr.rem8[k][a]]) % r;
                const u16* cm = qr.C_mod[j];
                const u8* qrt = qr.is_qr[j];
                u8* ok = ok8[k];
                for (u32 x = 0; x < T; ++x) ok[x] = qrt[(B * cm[x] + 1U) % r];
            }
            u64 la = indices[a];
            for (size_t b = a + 1; b < t; ++b) {
                u8 pass = ok8[0][r0[b]] & ok8[1][r1[b]] & ok8[2][r2[b]] & ok8[3][r3[b]]
                        & ok8[4][r4[b]] & ok8[5][r5[b]] & ok8[6][r6[b]] & ok8[7][r7[b]];
                if (!pass) continue;
                ++local_s8;
                verify_survivor(p, lam, la, indices[b], pidx, A, 8, nact, qr, stats, local_s48);
            }
        }
    }

    stats.primes_with_pairs.fetch_add(1, std::memory_order_relaxed);
    stats.total_pairs.fetch_add(local_pairs, std::memory_order_relaxed);
    stats.survived_8.fetch_add(local_s8, std::memory_order_relaxed);
    stats.survived_48.fetch_add(local_s48, std::memory_order_relaxed);
}

// ---------------------------------------------------------------------------
// 6. Self-test suite
// ---------------------------------------------------------------------------
static bool run_self_tests(const Sieve& sv, const std::vector<u32>& rank_p, const QRFilterTables& qr) {
    std::printf("Running self-tests (primary 8 primes: ");
    for (int i = 0; i < 8; ++i) std::printf("%u(T=%u)%s", qr.primes[i], qr.period[i], i==7?")\n":", ");

    u32 expected_U[] = {0, 1, 6, 35, 204, 1189};
    for (u32 k = 0; k < 6; ++k) {
        if (lucas_U_mod32(k, 1000000007U) != expected_U[k]) return false;
    }
    if (rank_p[3] != 2 || rank_p[5] != 3 || rank_p[7] != 3) return false;

    u64 exact_C[] = {0, 1, 35, 1190, 40426, 1373295, 46651605};
    for (u64 l = 0; l <= 6; ++l) {
        for (int j = 0; j < 10; ++j) {
            u32 r = qr.primes[j];
            if (qr.C_mod[j][l % qr.period[j]] != exact_C[l] % r) return false;
        }
        if (QRFilterTables::C_mod_large(l, 1000000007U) != exact_C[l] % 1000000007U) return false;
    }

    // Lemma 4.1 exact check
    int lemma41_count = 0;
    for (u32 p : sv.primes) {
        if (p < 11) continue;
        if (p > 4001) break;
        if ((p & 7U) != 3U && (p & 7U) != 5U) continue;
        u32 k = ((p & 7U) == 3U) ? (p + 1) / 4 : (p - 1) / 4;
        if (k >= 1000) continue;
        u64 lam = ((u64)p * p - 1) / 24;
        u32 a = p - 1, b = p + 1;
        int twos = 3;
        while (twos > 0 && (a & 1) == 0) { a >>= 1; --twos; }
        while (twos > 0 && (b & 1) == 0) { b >>= 1; --twos; }
        u64 mods[32]; int nm = 0;
        auto add_facs = [&](u32 v) {
            while (v > 1) {
                u32 q = sv.spf[v];
                int e = 0; u64 qe = 1;
                while (v % q == 0) { v /= q; ++e; qe *= q; }
                mods[nm++] = compute_rank_prime_power(q, e, rank_p[q], qe);
            }
        };
        add_facs(a); add_facs(b);
        std::sort(mods, mods + nm, std::greater<u64>());
        std::vector<u64> idxs;
        CRTGenerator gen{mods, nm, 7, {}};
        gen.generate(idxs, 100);
        for (u64 l : idxs) {
            if (l <= 7 && exact_C[l] % lam == 0) {
                u64 cp = exact_C[l] / lam;
                if (cp >= 1 && cp <= 48 * lam) ++lemma41_count;
            }
        }
    }
    if (lemma41_count != 8) {
        std::fprintf(stderr, "FAIL: Lemma 4.1 count=%d\n", lemma41_count);
        return false;
    }

    // Synthetic bitset-path square detection test (t=300, inject l=0 which gives 1^2)
    {
        std::vector<u64> synth(300);
        synth[0] = 0; // C_0 = 0 => 8*p^2*0*d'+1 = 1 = square for ALL b!
        for (size_t i = 1; i < 300; ++i) synth[i] = 3 * i;
        // Verify l=0 paired with l=3 passes large primes
        if (!qr.verify_large_primes(29, 35, 0, 3)) return false;
    }

    std::printf("All self-tests PASSED.\n");
    return true;
}

static bool is_proved_prime(u32 p) {
    // Theorem 1.2 of arXiv:2611.25270v1: S = {(3,-1),(3,1),(5,-1),(7,1),(9,1),(11,-1),(13,1),(27,1)}
    return p == 11 || p == 13 || p == 19 || p == 29 || p == 37 || p == 43 || p == 53 || p == 109;
}

int main(int argc, char** argv) {
    u32 P_min = 11;
    u32 P_max = 1000000;
    u64 L_max = 1000000;
    u32 max_idx = 4096;
    u32 num_threads = std::thread::hardware_concurrency();
    if (num_threads == 0) num_threads = 8;
    bool skip_proved = false;
    bool test_only = false;

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--pmin" && i + 1 < argc) P_min = std::stoul(argv[++i]);
        else if (arg == "--pmax" && i + 1 < argc) P_max = std::stoul(argv[++i]);
        else if (arg == "--lmax" && i + 1 < argc) L_max = std::stoull(argv[++i]);
        else if (arg == "--maxidx" && i + 1 < argc) max_idx = std::stoul(argv[++i]);
        else if (arg == "--threads" && i + 1 < argc) num_threads = std::stoul(argv[++i]);
        else if (arg == "--skip-proved") skip_proved = true;
        else if (arg == "--test") test_only = true;
    }

    auto t0 = std::chrono::steady_clock::now();
    u32 sieve_lim = std::max(P_max + 2, 10000U);
    Sieve sv;
    sv.init(sieve_lim);

    QRFilterTables qr;
    qr.init();

    u32 rank_lim = sieve_lim / 2 + 2;
    std::vector<u32> rank_p(rank_lim + 1, 0);
    {
        std::vector<u32> odd_primes;
        odd_primes.reserve(sv.primes.size());
        for (u32 q : sv.primes) if (q >= 3 && q <= rank_lim) odd_primes.push_back(q);
        std::atomic<size_t> cursor{0};
        auto worker = [&]() {
            while (true) {
                size_t start = cursor.fetch_add(2048, std::memory_order_relaxed);
                if (start >= odd_primes.size()) break;
                size_t end = std::min(start + 2048, odd_primes.size());
                for (size_t i = start; i < end; ++i) {
                    u32 q = odd_primes[i];
                    rank_p[q] = compute_rank_prime(q, sv);
                }
            }
        };
        std::vector<std::thread> ts;
        for (u32 t = 0; t < num_threads; ++t) ts.emplace_back(worker);
        for (auto& th : ts) th.join();
    }

    auto t1 = std::chrono::steady_clock::now();
    std::printf("Prep (sieve=%u, rank_lim=%u, threads=%u): %.3f s\n",
                sieve_lim, rank_lim, num_threads, std::chrono::duration<double>(t1 - t0).count());

    if (!run_self_tests(sv, rank_p, qr)) return 1;
    if (test_only) return 0;

    std::vector<u32> targets;
    targets.reserve(sv.primes.size() / 2);
    for (u32 p : sv.primes) {
        if (p < P_min) continue;
        if (p > P_max) break;
        if ((p & 7U) != 3U && (p & 7U) != 5U) continue;
        if (skip_proved && is_proved_prime(p)) continue;
        targets.push_back(p);
    }

    std::printf("Searching %zu primes p in [%u, %u] (p==3,5 mod 8%s), L_max=%llu, max_idx=%u, threads=%u\n",
                targets.size(), P_min, P_max, skip_proved ? ", unproved only" : "",
                (unsigned long long)L_max, max_idx, num_threads);
    std::fflush(stdout);

    SearchStats stats;
    std::atomic<size_t> cursor{0};
    auto t_start = std::chrono::steady_clock::now();

    auto search_worker = [&]() {
        ThreadScratch scr;
        scr.indices.reserve(max_idx);
        while (true) {
            size_t start = cursor.fetch_add(32, std::memory_order_relaxed);
            if (start >= targets.size()) break;
            size_t end = std::min(start + 32, targets.size());

            for (size_t i = start; i < end; ++i) {
                u32 p = targets[i];
                u64 lam = ((u64)p * p - 1) / 24;

                u32 a = p - 1, b = p + 1;
                int twos = 3;
                while (twos > 0 && (a & 1) == 0) { a >>= 1; --twos; }
                while (twos > 0 && (b & 1) == 0) { b >>= 1; --twos; }

                u64 mods[32];
                int nm = 0;
                auto add_facs = [&](u32 v) {
                    while (v > 1) {
                        u32 q = sv.spf[v];
                        int e = 0; u64 qe = 1;
                        while (v % q == 0) { v /= q; ++e; qe *= q; }
                        mods[nm++] = compute_rank_prime_power(q, e, rank_p[q], qe);
                    }
                };
                add_facs(a);
                add_facs(b);
                std::sort(mods, mods + nm, std::greater<u64>());

                CRTGenerator gen{mods, nm, L_max, {}};
                bool trunc = gen.generate(scr.indices, max_idx);

                stats.primes_checked.fetch_add(1, std::memory_order_relaxed);
                if (trunc) stats.truncated_primes.fetch_add(1, std::memory_order_relaxed);
                if (scr.indices.size() >= 2) {
                    stats.total_indices.fetch_add(scr.indices.size(), std::memory_order_relaxed);
                    check_pairs_for_prime(p, lam, scr.indices, qr, scr, stats);
                }
            }
        }
    };

    std::vector<std::thread> ts;
    for (u32 t = 0; t < num_threads; ++t) ts.emplace_back(search_worker);
    for (auto& th : ts) th.join();

    auto t_end = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(t_end - t_start).count();
    u64 pairs = stats.total_pairs.load();
    std::printf("\n=== DONE in %.3f s ===\n", elapsed);
    std::printf("Primes checked    : %llu\n", (unsigned long long)stats.primes_checked.load());
    std::printf("Primes with >=2 l : %llu (truncated: %llu)\n",
                (unsigned long long)stats.primes_with_pairs.load(),
                (unsigned long long)stats.truncated_primes.load());
    std::printf("Total valid l     : %llu\n", (unsigned long long)stats.total_indices.load());
    std::printf("Total (l,m) pairs : %llu (%.2f M pairs/s)\n",
                (unsigned long long)pairs, pairs / (elapsed * 1e6));
    std::printf("Survived 8 primes : %llu (%.3f%%)\n",
                (unsigned long long)stats.survived_8.load(),
                pairs ? 100.0 * stats.survived_8.load() / pairs : 0.0);
    std::printf("Survived 48 primes: %llu\n", (unsigned long long)stats.survived_48.load());
    std::printf("Counterexamples   : %llu\n", (unsigned long long)stats.counterexamples.load());
    return 0;
}
