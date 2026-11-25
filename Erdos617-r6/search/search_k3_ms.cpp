#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <mutex>
#include <random>
#include <thread>
#include <vector>

// Test k=3 Multi-Scale Single-Graph Relaxation:
// Find a K4-free graph F on n = 3r + 1 vertices with:
//   e(F) >= (r - 1) * (3r + 3) = 3r^2 - 3
//   min_{|S| = r+1} e(F[S]) >= r - 1
//   min_{|U| = 2r+1} e(F[U]) >= (r - 1)*(r + 2) = r^2 + r - 2

static inline int popcnt(uint32_t x) { return __builtin_popcount(x); }
static inline int ctz(uint32_t x) { return __builtin_ctz(x); }

int R, N, NEED_E, NEED_S, NEED_U;
std::vector<uint32_t> subs_S, subs_U;

void gen(int n, int k, int idx, uint32_t m, std::vector<uint32_t> &out) {
    if (k == 0) { out.push_back(m); return; }
    if (n - idx < k) return;
    gen(n, k - 1, idx + 1, m | (1u << idx), out);
    gen(n, k, idx + 1, m, out);
}

bool creates_k4(const uint32_t *adj, int u, int v) {
    uint32_t cn = adj[u] & adj[v];
    uint32_t t = cn;
    while (t) {
        int x = ctz(t); t &= t - 1;
        if (adj[x] & cn) return true;
    }
    return false;
}

struct Eval {
    int bad_S, def_S, min_S;
    int bad_U, def_U, min_U;
    uint32_t samp_S, samp_U;
};

Eval evaluate(const uint32_t *adj, std::mt19937_64 &rng) {
    Eval ev{0, 0, 1000000, 0, 0, 1000000, 0, 0};
    for (uint32_t m : subs_S) {
        int e2 = 0; uint32_t t = m;
        while (t) { int u = ctz(t); t &= t - 1; e2 += popcnt(adj[u] & m); }
        int e = e2 >> 1;
        if (e < ev.min_S) ev.min_S = e;
        if (e < NEED_S) {
            ev.bad_S++; ev.def_S += (NEED_S - e);
            if (ev.bad_S == 1 || (rng() % ev.bad_S == 0)) ev.samp_S = m;
        }
    }
    for (uint32_t m : subs_U) {
        int e2 = 0; uint32_t t = m;
        while (t) { int u = ctz(t); t &= t - 1; e2 += popcnt(adj[u] & m); }
        int e = e2 >> 1;
        if (e < ev.min_U) ev.min_U = e;
        if (e < NEED_U) {
            ev.bad_U++; ev.def_U += (NEED_U - e);
            if (ev.bad_U == 1 || (rng() % ev.bad_U == 0)) ev.samp_U = m;
        }
    }
    return ev;
}

int main(int argc, char **argv) {
    R = (argc >= 2) ? std::atoi(argv[1]) : 4;
    double time_lim = (argc >= 3) ? std::atof(argv[2]) : 8.0;
    N = 3 * R + 1;
    NEED_E = 3 * R * R - 3;
    NEED_S = R - 1;
    NEED_U = R * R + R - 2;
    gen(N, R + 1, 0, 0, subs_S);
    gen(N, 2 * R + 1, 0, 0, subs_U);
    std::cout << "k=3 Multi-Scale test: r=" << R << " n=" << N
              << " need_e>=" << NEED_E << " need_S>=" << NEED_S << " (" << subs_S.size() << ")"
              << " need_U>=" << NEED_U << " (" << subs_U.size() << ")\n" << std::flush;

    std::atomic<bool> found{false};
    std::atomic<int> best_bad{1000000000};
    std::mutex mtx;
    auto t0 = std::chrono::steady_clock::now();

    auto worker = [&](int tid) {
        std::mt19937_64 rng(0xabcdef12345ULL * (tid + 1) ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());
        while (!found.load()) {
            if (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() >= time_lim) break;
            uint32_t adj[32] = {0};
            int edges = 0;
            // Random maximal K4-free graph
            std::vector<std::pair<int,int>> pairs;
            for (int i = 0; i < N; ++i)
                for (int j = i + 1; j < N; ++j) pairs.push_back({i, j});
            std::shuffle(pairs.begin(), pairs.end(), rng);
            for (auto [u, v] : pairs) {
                if (!creates_k4(adj, u, v)) {
                    adj[u] |= (1u << v); adj[v] |= (1u << u); edges++;
                }
            }
            Eval cur = evaluate(adj, rng);
            auto score_fn = [&](const Eval &ev, int e) -> double {
                double pe = (e < NEED_E) ? 20.0 * (NEED_E - e) : 0.0;
                double pmin = (ev.min_S < NEED_S ? 50.0 * (NEED_S - ev.min_S) : 0.0)
                            + (ev.min_U < NEED_U ? 50.0 * (NEED_U - ev.min_U) : 0.0);
                return pe + pmin + ev.bad_S + ev.bad_U + 2.0 * (ev.def_S + ev.def_U);
            };
            double cur_s = score_fn(cur, edges);
            double temp = 5.0;
            int stale = 0;

            for (int step = 0; step < 10000 && !found.load(); ++step) {
                if (edges >= NEED_E && cur.bad_S == 0 && cur.bad_U == 0) {
                    if (!found.exchange(true)) {
                        std::lock_guard<std::mutex> lk(mtx);
                        std::cout << "=== WITNESS FOUND r=" << R << " e=" << edges
                                  << " min_S=" << cur.min_S << " min_U=" << cur.min_U << " ===\n" << std::flush;
                    }
                    return;
                }
                int tot = cur.bad_S + cur.bad_U;
                if (edges >= NEED_E && tot < best_bad.load()) {
                    std::lock_guard<std::mutex> lk(mtx);
                    if (tot < best_bad.load()) {
                        best_bad.store(tot);
                        std::cout << "[tid=" << tid << "] NEW BEST bad=" << tot
                                  << " (bS=" << cur.bad_S << " mS=" << cur.min_S
                                  << ", bU=" << cur.bad_U << " mU=" << cur.min_U
                                  << ", e=" << edges << ")\n" << std::flush;
                    }
                }

                // Pick a non-edge (au, av) to force-add, prefer inside bad subset
                int au = -1, av = -1;
                uint32_t m = (cur.bad_S > 0 && (cur.bad_U == 0 || (rng() & 1))) ? cur.samp_S : cur.samp_U;
                if (m && (rng() % 100) < 75) {
                    int vs[32], vc = 0; uint32_t t = m;
                    while (t) { vs[vc++] = ctz(t); t &= t - 1; }
                    for (int tr = 0; tr < 15; ++tr) {
                        int a = vs[rng() % vc], b = vs[rng() % vc];
                        if (a != b && !((adj[a] >> b) & 1u)) { au = a; av = b; break; }
                    }
                }
                if (au == -1) {
                    for (int tr = 0; tr < 20; ++tr) {
                        int a = rng() % N, b = rng() % N;
                        if (a != b && !((adj[a] >> b) & 1u)) { au = a; av = b; break; }
                    }
                }
                if (au == -1) continue;

                uint32_t old_adj[32];
                std::copy(adj, adj + N, old_adj);
                int old_e = edges;

                // Break all K4's created by (au, av): while common neighbors have an edge (x,y), remove one of (au,x),(au,y),(av,x),(av,y),(x,y)
                int guard = 0;
                while (guard++ < 200) {
                    uint32_t cn = adj[au] & adj[av];
                    int bx = -1, by = -1;
                    uint32_t t = cn;
                    while (t) {
                        int x = ctz(t); t &= t - 1;
                        uint32_t ys = adj[x] & cn;
                        if (ys) { bx = x; by = ctz(ys); break; }
                    }
                    if (bx == -1) break;
                    int choice = rng() % 5;
                    int p, q;
                    if (choice == 0) { p = au; q = bx; }
                    else if (choice == 1) { p = au; q = by; }
                    else if (choice == 2) { p = av; q = bx; }
                    else if (choice == 3) { p = av; q = by; }
                    else { p = bx; q = by; }
                    adj[p] &= ~(1u << q); adj[q] &= ~(1u << p); edges--;
                }
                adj[au] |= (1u << av); adj[av] |= (1u << au); edges++;

                // Greedily saturate to maximal K4-free
                std::vector<std::pair<int,int>> cands;
                for (int i = 0; i < N; ++i) {
                    uint32_t non = (~adj[i]) & ((1u << N) - 1u) & ~((1u << (i + 1)) - 1u);
                    while (non) {
                        int j = ctz(non); non &= non - 1;
                        if (!creates_k4(adj, i, j)) cands.push_back({i, j});
                    }
                }
                if (!cands.empty()) {
                    std::shuffle(cands.begin(), cands.end(), rng);
                    for (auto [x, y] : cands) {
                        if (!creates_k4(adj, x, y)) {
                            adj[x] |= (1u << y); adj[y] |= (1u << x); edges++;
                        }
                    }
                }

                Eval nxt = evaluate(adj, rng);
                double nxt_s = score_fn(nxt, edges);
                double delta = nxt_s - cur_s;
                bool acc = (delta <= 0.0);
                if (!acc && temp > 1e-4) {
                    double u01 = (double)(rng() >> 11) * (1.0 / (double)(1ULL << 53));
                    acc = (u01 < std::exp(-delta / temp));
                }
                if (acc) {
                    cur = nxt; cur_s = nxt_s;
                    if (delta < 0) stale = 0; else stale++;
                } else {
                    std::copy(old_adj, old_adj + N, adj);
                    edges = old_e;
                    stale++;
                }
                temp = std::max(0.05, temp * 0.999);
                if (stale > 1200) break;
            }
        }
    };

    std::vector<std::thread> pool;
    for (int t = 0; t < 20; ++t) pool.emplace_back(worker, t);
    for (auto &th : pool) th.join();
    std::cout << "Done r=" << R << " found=" << (found.load() ? "YES" : "NO")
              << " best_bad=" << best_bad.load() << "\n";
    return 0;
}
