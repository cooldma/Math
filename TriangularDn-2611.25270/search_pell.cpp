// search_pell.cpp
// Searches ALL Pell primes p = Q_l = P_{2l+1} (l == 1 or 2 mod 4, so p == 5 mod 8)
// where lambda = C_l and c' = 1, testing m along all 4 CRT residue classes
// m == 0, -1, l, -(l+1) (mod l*(l+1)) up to M_max (e.g. 10^9 -> 1.5-billion-digit d!).
//
// Build:
//   g++ -O3 -march=native -flto -std=c++20 -pthread search_pell.cpp -o search_pell.exe

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

using u8   = uint8_t;
using u16  = uint16_t;
using u32  = uint32_t;
using u64  = uint64_t;
using u128 = __uint128_t;

static constexpr int NUM_PRIMES   = 64;
static constexpr int NUM_CHECK    = 48;
static constexpr int MAX_SMALL_P  = 1600;
static constexpr int MAX_PERIOD   = 800;
static constexpr int NUM_LARGE_P  = 64;

static inline u64 mulmod64(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

static u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1; a %= m;
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
    for (u32 d = 3; (u64)d * d <= n; d += 2) if (n % d == 0) return false;
    return true;
}

// Compute (U_k, U_{k+1}) mod r where U_0=0, U_1=1, U_{k+1}=6*U_k - U_{k-1}
static std::pair<u64, u64> lucas_pair_mod(u64 k, u32 r) {
    if (k == 0) return {0, 1};
    u64 u0 = 0, u1 = 1;
    int top = 63 - __builtin_clzll(k);
    for (int bit = top; bit >= 0; --bit) {
        u64 t = (2 * u1 + 6ULL * r - 6 * u0) % r;
        u64 u2n = (u0 * t) % r;
        u64 s1 = (u1 * u1) % r;
        u64 s0 = (u0 * u0) % r;
        u64 u2n1 = (s1 >= s0) ? (s1 - s0) : (s1 + r - s0);
        if ((k >> bit) & 1ULL) {
            u0 = u2n1;
            u64 six = (6 * u2n1) % r;
            u1 = (six >= u2n) ? (six - u2n) : (six + r - u2n);
        } else {
            u0 = u2n;
            u1 = u2n1;
        }
    }
    return {u0, u1};
}

// C_l mod r = U_l * U_{l+1} * inv(6, r)
static u64 C_mod_r(u64 l, u32 r) {
    auto [u0, u1] = lucas_pair_mod(l, r);
    u64 inv6 = powmod(6, r - 2, r);
    return (((u0 * u1) % r) * inv6) % r;
}

// Q_l^2 mod r = 24 * C_l + 1 (mod r)
static u64 Q2_mod_r(u64 l, u32 r) {
    return (24ULL * C_mod_r(l, r) + 1ULL) % r;
}

struct Tables {
    u32 primes[NUM_PRIMES];
    u32 period[NUM_PRIMES];
    u16 C_mod[NUM_PRIMES][MAX_PERIOD];
    u8  is_qr[NUM_PRIMES][MAX_SMALL_P];
    u32 large_primes[NUM_LARGE_P];

    static u32 find_period(u32 p, u16* out_C) {
        u32 c0 = 0, c1 = 1;
        out_C[0] = 0;
        for (u32 l = 1; l < MAX_PERIOD; ++l) {
            out_C[l] = (u16)c1;
            u32 c2 = (34U * c1 + p - c0 + 1U) % p;
            c0 = c1; c1 = c2;
            if (c0 == 0 && c1 == 1) return l;
        }
        return 0;
    }

    void init() {
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
        for (u32 p : tier0) if (chosen.size() < NUM_PRIMES) chosen.push_back(p);
        for (u32 p : tier1) if (chosen.size() < NUM_PRIMES) chosen.push_back(p);
        for (u32 p : tier2) if (chosen.size() < NUM_PRIMES) chosen.push_back(p);
        for (int i = 0; i < NUM_PRIMES; ++i) {
            u32 p = chosen[i];
            primes[i] = p;
            std::memset(is_qr[i], 0, sizeof(is_qr[i]));
            for (u32 x = 0; x < p; ++x) is_qr[i][(x * x) % p] = 1;
            period[i] = find_period(p, C_mod[i]);
        }
        int li = 0;
        for (u32 p = 1000000007U; li < NUM_LARGE_P; p += 2) {
            if (is_prime_u32(p)) large_primes[li++] = p;
        }
    }

    bool verify_large(u64 ell, u64 m) const {
        for (int i = 0; i < NUM_LARGE_P; ++i) {
            u32 r = large_primes[i];
            u64 cl = C_mod_r(ell, r);
            if (cl == 0) continue;
            u64 q2 = (24ULL * cl + 1ULL) % r;
            u64 cm = C_mod_r(m, r);
            u64 inv_cl = powmod(cl, r - 2, r);
            u64 val = (((8ULL * q2 % r) * inv_cl % r) * cm + 1ULL) % r;
            if (val != 0 && powmod(val, (r - 1) >> 1, r) != 1) return false;
        }
        return true;
    }
};

int main(int argc, char** argv) {
    u64 max_steps = 10000000; // steps per residue class (so m up to max_steps * ell * (ell+1))
    std::vector<u64> ells;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--steps" && i + 1 < argc) max_steps = std::stoull(argv[++i]);
        else ells.push_back(std::stoull(a));
    }
    if (ells.empty()) {
        std::fprintf(stderr, "Usage: search_pell --steps N ell1 ell2 ...\n");
        return 1;
    }

    Tables tb;
    tb.init();

    u64 total_checked = 0;
    u64 total_hits = 0;
    auto t0 = std::chrono::steady_clock::now();

    for (u64 ell : ells) {
        // Select first 48 helper primes with C_ell != 0 (mod r)
        int pidx[NUM_CHECK];
        u32 B[NUM_CHECK];
        int nact = 0;
        for (int j = 0; j < NUM_PRIMES && nact < NUM_CHECK; ++j) {
            u32 r = tb.primes[j];
            u32 cl = tb.C_mod[j][ell % tb.period[j]];
            if (cl == 0) continue;
            u64 q2 = (24ULL * cl + 1ULL) % r;
            u64 inv_cl = powmod(cl, r - 2, r);
            pidx[nact] = j;
            B[nact] = (u32)((8ULL * q2 % r) * inv_cl % r);
            ++nact;
        }

        // Build ok8[k][x] for first 8 primes
        u8 ok8[8][MAX_PERIOD];
        u32 T8[8];
        for (int k = 0; k < 8; ++k) {
            int j = pidx[k];
            u32 r = tb.primes[j];
            u32 T = tb.period[j];
            T8[k] = T;
            for (u32 x = 0; x < T; ++x) {
                ok8[k][x] = tb.is_qr[j][(B[k] * tb.C_mod[j][x] + 1U) % r];
            }
        }

        u64 modM = ell * (ell + 1);
        u64 starts[4] = { modM, modM - 1, modM + ell, modM - ell - 1 };
        // Also check m = ell + ... (ensure m > ell)
        u64 ell_hits = 0;
        u64 ell_checked = 0;

        for (int s = 0; s < 4; ++s) {
            u64 m0 = starts[s];
            while (m0 <= ell) m0 += modM;
            u32 step8[8], cur8[8];
            for (int k = 0; k < 8; ++k) {
                step8[k] = (u32)(modM % T8[k]);
                cur8[k]  = (u32)(m0 % T8[k]);
            }
            for (u64 step = 0; step < max_steps; ++step) {
                u8 pass = ok8[0][cur8[0]] & ok8[1][cur8[1]] & ok8[2][cur8[2]] & ok8[3][cur8[3]]
                        & ok8[4][cur8[4]] & ok8[5][cur8[5]] & ok8[6][cur8[6]] & ok8[7][cur8[7]];
                if (pass) {
                    u64 m = m0 + step * modM;
                    bool ok = true;
                    for (int k = 8; k < nact; ++k) {
                        int j = pidx[k];
                        u32 r = tb.primes[j];
                        u32 T = tb.period[j];
                        u32 cm = tb.C_mod[j][m % T];
                        if (!tb.is_qr[j][(B[k] * cm + 1U) % r]) { ok = false; break; }
                    }
                    if (ok && tb.verify_large(ell, m)) {
                        ++ell_hits;
                        std::printf("[!!! PELL COUNTEREXAMPLE !!!] ell=%llu m=%llu\n",
                                    (unsigned long long)ell, (unsigned long long)m);
                        std::fflush(stdout);
                    }
                }
                for (int k = 0; k < 8; ++k) {
                    cur8[k] += step8[k];
                    if (cur8[k] >= T8[k]) cur8[k] -= T8[k];
                }
            }
            ell_checked += max_steps;
        }
        total_checked += ell_checked;
        total_hits += ell_hits;
        u64 max_m = modM * max_steps;
        std::printf("Pell prime Q_%llu (mod=%llu): checked %llu values up to m~%llu, hits=%llu\n",
                    (unsigned long long)ell, (unsigned long long)modM,
                    (unsigned long long)ell_checked, (unsigned long long)max_m,
                    (unsigned long long)ell_hits);
    }

    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("=== PELL SEARCH DONE in %.3f s: %zu Pell primes, %llu candidates (%.1f M/s), hits=%llu ===\n",
                dt, ells.size(), (unsigned long long)total_checked, total_checked / (dt * 1e6),
                (unsigned long long)total_hits);
    return 0;
}
