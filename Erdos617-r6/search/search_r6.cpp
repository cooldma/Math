#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <vector>

// Fast multi-threaded local search for Erdős #617 single-graph relaxation.
// Finds a graph G on N vertices with:
//   e(G) <= MAX_EDGES
//   alpha(G) <= MAX_ALPHA  (no independent set of size MAX_ALPHA + 1)
//   max_{|S| = R+1} e(G[S]) <= MAX_SUB_EDGES
// Specialized for R = 6 (7-subsets, MAX_SUB_EDGES = 16), works for any N <= 63
// and any MAX_ALPHA <= 6 (e.g. disjoint union H + (6-k) K_6 with N = 6k+1, MAX_ALPHA = k).

struct Config {
    int N = 37;
    int MAX_ALPHA = 6;
    int MAX_EDGES = 111;
    int MAX_SUB_EDGES = 16; // for 7-subsets
    int THREADS = 20;
    double TIME_LIMIT_SEC = 60.0;
    int INIT_MODE = 0; // 0: mixed, 1: turan_perturbed, 2: random_regular, 3: k4_free_bias, 4: c5_blowup
};

struct Graph {
    int n;
    uint64_t adj[64];
    uint64_t non_adj[64];
    uint64_t all_mask;
    int edges;
    int deg[64];

    void init(int n_) {
        n = n_;
        all_mask = (n == 64) ? ~0ULL : ((1ULL << n) - 1ULL);
        edges = 0;
        for (int i = 0; i < n; ++i) {
            adj[i] = 0;
            non_adj[i] = all_mask & ~(1ULL << i);
            deg[i] = 0;
        }
    }

    inline bool has_edge(int u, int v) const {
        return (adj[u] >> v) & 1ULL;
    }

    inline void add_edge(int u, int v) {
        if (u == v || has_edge(u, v)) return;
        adj[u] |= (1ULL << v);
        adj[v] |= (1ULL << u);
        non_adj[u] &= ~(1ULL << v);
        non_adj[v] &= ~(1ULL << u);
        deg[u]++;
        deg[v]++;
        edges++;
    }

    inline void remove_edge(int u, int v) {
        if (u == v || !has_edge(u, v)) return;
        adj[u] &= ~(1ULL << v);
        adj[v] &= ~(1ULL << u);
        non_adj[u] |= (1ULL << v);
        non_adj[v] |= (1ULL << u);
        deg[u]--;
        deg[v]--;
        edges--;
    }
};

struct EvalResult {
    int ind_cnt;      // number of independent sets of size MAX_ALPHA+1 (capped)
    int dense_cnt;    // number of 7-sets with >= 17 edges (capped)
    int dense_excess; // sum of (e(S) - 16) over dense 7-sets
    uint64_t sample_ind;
    uint64_t sample_dense;
    int ind_seen;
    int dense_seen;
};

static inline int popcnt(uint64_t x) {
    return __builtin_popcountll(x);
}
static inline int ctz(uint64_t x) {
    return __builtin_ctzll(x);
}

// Recursive count of independent sets of size `rem` inside `cand`, recording a reservoir sample.
void dfs_ind(const Graph &g, int rem, uint64_t cand, uint64_t cur_mask,
             int &cnt, int cap, uint64_t &sample, std::mt19937_64 &rng) {
    if (cnt >= cap) return;
    int pc = popcnt(cand);
    if (pc < rem) return;
    if (rem == 1) {
        while (cand) {
            int u = ctz(cand);
            cand &= cand - 1;
            cnt++;
            if (cnt == 1 || (rng() % cnt == 0)) {
                sample = cur_mask | (1ULL << u);
            }
            if (cnt >= cap) return;
        }
        return;
    }
    if (rem == 2) {
        while (cand) {
            int u = ctz(cand);
            cand &= cand - 1;
            uint64_t c2 = cand & g.non_adj[u];
            while (c2) {
                int v = ctz(c2);
                c2 &= c2 - 1;
                cnt++;
                if (cnt == 1 || (rng() % cnt == 0)) {
                    sample = cur_mask | (1ULL << u) | (1ULL << v);
                }
                if (cnt >= cap) return;
            }
        }
        return;
    }
    while (cand) {
        if (popcnt(cand) < rem) return;
        int u = ctz(cand);
        cand &= cand - 1;
        dfs_ind(g, rem - 1, cand & g.non_adj[u], cur_mask | (1ULL << u), cnt, cap, sample, rng);
        if (cnt >= cap) return;
    }
}

// Fast exact count of 7-subsets with >= 17 edges (for R = 6, MAX_SUB_EDGES = 16).
// Every 7-set S with e(S) >= 17 has max internal degree >= 5.
// Canonical representative: smallest vertex u in S attaining max internal degree in S.
void count_dense7(const Graph &g, int max_sub_edges, int cap,
                  int &dense_cnt, int &dense_excess, uint64_t &sample, std::mt19937_64 &rng) {
    dense_cnt = 0;
    dense_excess = 0;
    sample = 0;
    int thresh = max_sub_edges + 1; // 17

    int nbrs[64];
    for (int u = 0; u < g.n; ++u) {
        if (g.deg[u] < 5) continue;
        uint64_t nu = g.adj[u];
        int d = 0;
        uint64_t tmp = nu;
        while (tmp) {
            nbrs[d++] = ctz(tmp);
            tmp &= tmp - 1;
        }

        // Case 1: d_S(u) == 6 -> choose 6 neighbors of u.
        // e(S) = 6 + e(A) >= thresh  <=>  e(A) >= thresh - 6 = 11.
        // Canonical: no v < u in A has d_A(v) == 5 (since u is adjacent to all of A, d_S(v) = 1 + d_A(v)).
        if (d >= 6) {
            int needA = thresh - 6;
            for (int i0 = 0; i0 < d - 5; ++i0) {
                int v0 = nbrs[i0];
                uint64_t a0 = g.adj[v0];
                for (int i1 = i0 + 1; i1 < d - 4; ++i1) {
                    int v1 = nbrs[i1];
                    int e01 = (a0 >> v1) & 1;
                    uint64_t a1 = g.adj[v1];
                    for (int i2 = i1 + 1; i2 < d - 3; ++i2) {
                        int v2 = nbrs[i2];
                        int e012 = e01 + ((a0 >> v2) & 1) + ((a1 >> v2) & 1);
                        uint64_t a2 = g.adj[v2];
                        for (int i3 = i2 + 1; i3 < d - 2; ++i3) {
                            int v3 = nbrs[i3];
                            int e0123 = e012 + ((a0 >> v3) & 1) + ((a1 >> v3) & 1) + ((a2 >> v3) & 1);
                            if (e0123 + 9 < needA) continue; // at most 9 edges remain
                            uint64_t a3 = g.adj[v3];
                            for (int i4 = i3 + 1; i4 < d - 1; ++i4) {
                                int v4 = nbrs[i4];
                                int e01234 = e0123 + ((a0 >> v4) & 1) + ((a1 >> v4) & 1) + ((a2 >> v4) & 1) + ((a3 >> v4) & 1);
                                if (e01234 + 5 < needA) continue;
                                uint64_t a4 = g.adj[v4];
                                for (int i5 = i4 + 1; i5 < d; ++i5) {
                                    int v5 = nbrs[i5];
                                    int eA = e01234 + ((a0 >> v5) & 1) + ((a1 >> v5) & 1) + ((a2 >> v5) & 1) + ((a3 >> v5) & 1) + ((a4 >> v5) & 1);
                                    if (eA < needA) continue;
                                    uint64_t maskA = (1ULL << v0) | (1ULL << v1) | (1ULL << v2) | (1ULL << v3) | (1ULL << v4) | (1ULL << v5);
                                    // Canonical check: no v < u in A has popcnt(adj[v] & maskA) == 5
                                    bool canon = true;
                                    int vs[6] = {v0, v1, v2, v3, v4, v5};
                                    for (int k = 0; k < 6; ++k) {
                                        if (vs[k] < u && popcnt(g.adj[vs[k]] & maskA) == 5) {
                                            canon = false;
                                            break;
                                        }
                                    }
                                    if (!canon) continue;
                                    dense_cnt++;
                                    dense_excess += (6 + eA - max_sub_edges);
                                    if (dense_cnt == 1 || (rng() % dense_cnt == 0)) {
                                        sample = maskA | (1ULL << u);
                                    }
                                    if (dense_cnt >= cap) return;
                                }
                            }
                        }
                    }
                }
            }
        }

        // Case 2: d_S(u) == 5, and max internal degree in S is 5 (no vertex has d_S == 6).
        // Choose 5 neighbors A of u, and 1 non-neighbor w of u.
        // e(S) = 5 + e(A) + d_A(w) >= thresh  <=>  e(A) + d_A(w) >= thresh - 5 = 12.
        // Since d_A(w) <= 5, we need e(A) >= thresh - 10 = 7.
        int needSum = thresh - 5; // 12
        int minEA = needSum - 5;  // 7
        uint64_t non_u = g.non_adj[u];
        for (int i0 = 0; i0 < d - 4; ++i0) {
            int v0 = nbrs[i0];
            uint64_t a0 = g.adj[v0];
            for (int i1 = i0 + 1; i1 < d - 3; ++i1) {
                int v1 = nbrs[i1];
                int e01 = (a0 >> v1) & 1;
                uint64_t a1 = g.adj[v1];
                for (int i2 = i1 + 1; i2 < d - 2; ++i2) {
                    int v2 = nbrs[i2];
                    int e012 = e01 + ((a0 >> v2) & 1) + ((a1 >> v2) & 1);
                    if (e012 + 7 < minEA) continue;
                    uint64_t a2 = g.adj[v2];
                    for (int i3 = i2 + 1; i3 < d - 1; ++i3) {
                        int v3 = nbrs[i3];
                        int e0123 = e012 + ((a0 >> v3) & 1) + ((a1 >> v3) & 1) + ((a2 >> v3) & 1);
                        if (e0123 + 4 < minEA) continue;
                        uint64_t a3 = g.adj[v3];
                        for (int i4 = i3 + 1; i4 < d; ++i4) {
                            int v4 = nbrs[i4];
                            int eA = e0123 + ((a0 >> v4) & 1) + ((a1 >> v4) & 1) + ((a2 >> v4) & 1) + ((a3 >> v4) & 1);
                            if (eA < minEA) continue;
                            uint64_t a4 = g.adj[v4];
                            int needW = needSum - eA; // >= 2
                            uint64_t maskA = (1ULL << v0) | (1ULL << v1) | (1ULL << v2) | (1ULL << v3) | (1ULL << v4);
                            // Candidate w in non_u with >= 2 neighbors in A
                            uint64_t cands = non_u & (a0 | a1 | a2 | a3 | a4);
                            // Precompute degrees of v0..v4 inside A
                            int dA[5] = {
                                popcnt(a0 & maskA),
                                popcnt(a1 & maskA),
                                popcnt(a2 & maskA),
                                popcnt(a3 & maskA),
                                popcnt(a4 & maskA)
                            };
                            int vs[5] = {v0, v1, v2, v3, v4};
                            while (cands) {
                                int w = ctz(cands);
                                cands &= cands - 1;
                                int dw = popcnt(g.adj[w] & maskA);
                                if (dw < needW) continue;
                                // Check no vertex in S has d_S == 6 and no vertex < u has d_S == 5.
                                // Note d_S(w) = dw (since w not adj to u).
                                // For v in A: d_S(v) = 1 + dA[k] + ((adj[w] >> v) & 1).
                                if (dw == 5 && w < u) continue;
                                bool ok = true;
                                for (int k = 0; k < 5; ++k) {
                                    int dv = 1 + dA[k] + (int)((g.adj[w] >> vs[k]) & 1ULL);
                                    if (dv == 6 || (dv == 5 && vs[k] < u)) {
                                        ok = false;
                                        break;
                                    }
                                }
                                if (!ok) continue;
                                dense_cnt++;
                                dense_excess += (5 + eA + dw - max_sub_edges);
                                if (dense_cnt == 1 || (rng() % dense_cnt == 0)) {
                                    sample = maskA | (1ULL << u) | (1ULL << w);
                                }
                                if (dense_cnt >= cap) return;
                            }
                        }
                    }
                }
            }
        }
    }
}

EvalResult evaluate(const Graph &g, const Config &cfg, int ind_cap, int dense_cap, std::mt19937_64 &rng) {
    EvalResult res{};
    dfs_ind(g, cfg.MAX_ALPHA + 1, g.all_mask, 0ULL, res.ind_cnt, ind_cap, res.sample_ind, rng);
    count_dense7(g, cfg.MAX_SUB_EDGES, dense_cap, res.dense_cnt, res.dense_excess, res.sample_dense, rng);
    return res;
}

// Brute force exact verifier for any candidate witness!
bool verify_exact(const Graph &g, const Config &cfg) {
    if (g.edges > cfg.MAX_EDGES) return false;
    std::mt19937_64 dummy(1);
    int ind_cnt = 0;
    uint64_t s1 = 0;
    dfs_ind(g, cfg.MAX_ALPHA + 1, g.all_mask, 0ULL, ind_cnt, 1, s1, dummy);
    if (ind_cnt > 0) return false;

    int dense_cnt = 0, dense_ex = 0;
    uint64_t s2 = 0;
    count_dense7(g, cfg.MAX_SUB_EDGES, 1, dense_cnt, dense_ex, s2, dummy);
    if (dense_cnt > 0) return false;
    return true;
}

// Independent brute-force check of count_dense7 on small N (unit test)
void self_test() {
    std::mt19937_64 rng(12345);
    int n = 15;
    for (int trial = 0; trial < 20; ++trial) {
        Graph g;
        g.init(n);
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                if ((rng() % 100) < 55) g.add_edge(i, j);
        int fast_cnt = 0, fast_ex = 0;
        uint64_t samp = 0;
        count_dense7(g, 16, 1000000, fast_cnt, fast_ex, samp, rng);

        // Brute force all C(15, 7) = 6435 subsets
        int bf_cnt = 0, bf_ex = 0;
        for (int a = 0; a < n; ++a)
        for (int b = a+1; b < n; ++b)
        for (int c = b+1; c < n; ++c)
        for (int d = c+1; d < n; ++d)
        for (int e = d+1; e < n; ++e)
        for (int f = e+1; f < n; ++f)
        for (int h = f+1; h < n; ++h) {
            uint64_t m = (1ULL<<a)|(1ULL<<b)|(1ULL<<c)|(1ULL<<d)|(1ULL<<e)|(1ULL<<f)|(1ULL<<h);
            int ec = (popcnt(g.adj[a]&m)+popcnt(g.adj[b]&m)+popcnt(g.adj[c]&m)+popcnt(g.adj[d]&m)
                     +popcnt(g.adj[e]&m)+popcnt(g.adj[f]&m)+popcnt(g.adj[h]&m)) / 2;
            if (ec >= 17) {
                bf_cnt++;
                bf_ex += (ec - 16);
            }
        }
        if (fast_cnt != bf_cnt || fast_ex != bf_ex) {
            std::cerr << "SELF TEST FAILED! trial=" << trial
                      << " fast=(" << fast_cnt << "," << fast_ex
                      << ") bf=(" << bf_cnt << "," << bf_ex << ")\n";
            std::exit(1);
        }
    }
    std::cout << "[self_test] count_dense7 exactness PASSED (20 random n=15 graphs)\n";
}

void init_graph(Graph &g, const Config &cfg, int mode, std::mt19937_64 &rng) {
    g.init(cfg.N);
    if (mode == 0) {
        // Turan-like: MAX_ALPHA cliques, then randomly add edges up to MAX_EDGES
        for (int i = 0; i < cfg.N; ++i) {
            for (int j = i + 1; j < cfg.N; ++j) {
                if (i % cfg.MAX_ALPHA == j % cfg.MAX_ALPHA) {
                    g.add_edge(i, j);
                }
            }
        }
        // Delete random edges from the largest clique (mod 0)
        std::vector<std::pair<int,int>> c0;
        for (int i = 0; i < cfg.N; i += cfg.MAX_ALPHA)
            for (int j = i + cfg.MAX_ALPHA; j < cfg.N; j += cfg.MAX_ALPHA)
                c0.push_back({i, j});
        std::shuffle(c0.begin(), c0.end(), rng);
        int del = std::min((int)c0.size(), 6);
        for (int k = 0; k < del; ++k) g.remove_edge(c0[k].first, c0[k].second);
    } else if (mode == 1) {
        // C5 blowup on 13 vertices + cliques on remaining
        if (cfg.N >= 13 && cfg.MAX_ALPHA >= 2) {
            int sz[5] = {3, 3, 2, 3, 2};
            int part[13];
            int idx = 0;
            for (int p = 0; p < 5; ++p)
                for (int c = 0; c < sz[p]; ++c) part[idx++] = p;
            for (int i = 0; i < 13; ++i)
                for (int j = i + 1; j < 13; ++j) {
                    int diff = std::abs(part[i] - part[j]);
                    if (diff == 0 || diff == 1 || diff == 4) g.add_edge(i, j);
                }
            int rem_cliques = cfg.MAX_ALPHA - 2;
            for (int c = 0; c < rem_cliques; ++c) {
                int base = 13 + 6 * c;
                for (int i = base; i < std::min(cfg.N, base + 6); ++i)
                    for (int j = i + 1; j < std::min(cfg.N, base + 6); ++j)
                        g.add_edge(i, j);
            }
        }
    } else if (mode == 2) {
        // Random graph with MAX_EDGES edges (no clique structure)
        std::vector<std::pair<int,int>> all_e;
        for (int i = 0; i < cfg.N; ++i)
            for (int j = i + 1; j < cfg.N; ++j) all_e.push_back({i, j});
        std::shuffle(all_e.begin(), all_e.end(), rng);
        for (int k = 0; k < cfg.MAX_EDGES && k < (int)all_e.size(); ++k)
            g.add_edge(all_e[k].first, all_e[k].second);
    } else {
        // Greedy K4-free random graph up to MAX_EDGES
        std::vector<std::pair<int,int>> all_e;
        for (int i = 0; i < cfg.N; ++i)
            for (int j = i + 1; j < cfg.N; ++j) all_e.push_back({i, j});
        std::shuffle(all_e.begin(), all_e.end(), rng);
        for (auto [u, v] : all_e) {
            if (g.edges >= cfg.MAX_EDGES) break;
            // check if u,v create K4: common neighbors contain an edge
            uint64_t cn = g.adj[u] & g.adj[v];
            bool mk4 = false;
            uint64_t t = cn;
            while (t) {
                int x = ctz(t);
                t &= t - 1;
                if (g.adj[x] & cn) { mk4 = true; break; }
            }
            if (!mk4) g.add_edge(u, v);
        }
    }

    // Adjust edge count to MAX_EDGES
    while (g.edges < cfg.MAX_EDGES) {
        int u = rng() % cfg.N;
        int v = rng() % cfg.N;
        if (u != v && !g.has_edge(u, v)) g.add_edge(u, v);
    }
    while (g.edges > cfg.MAX_EDGES) {
        int u = rng() % cfg.N;
        if (g.deg[u] == 0) continue;
        int k = rng() % g.deg[u];
        uint64_t m = g.adj[u];
        int v = -1;
        while (k-- >= 0) { v = ctz(m); m &= m - 1; }
        g.remove_edge(u, v);
    }
}

void print_graph(const Graph &g) {
    std::cout << "=== WITNESS FOUND: N=" << g.n << " E=" << g.edges << " ===\n";
    for (int u = 0; u < g.n; ++u) {
        std::cout << u << ":";
        for (int v = 0; v < g.n; ++v) {
            if (g.has_edge(u, v)) std::cout << " " << v;
        }
        std::cout << "\n";
    }
    std::cout << "EDGES=[";
    bool first = true;
    for (int u = 0; u < g.n; ++u) {
        for (int v = u + 1; v < g.n; ++v) {
            if (g.has_edge(u, v)) {
                if (!first) std::cout << ",";
                std::cout << "(" << u << "," << v << ")";
                first = false;
            }
        }
    }
    std::cout << "]\n" << std::flush;
}

int main(int argc, char **argv) {
    self_test();
    Config cfg;
    if (argc >= 4) {
        cfg.N = std::atoi(argv[1]);
        cfg.MAX_ALPHA = std::atoi(argv[2]);
        cfg.MAX_EDGES = std::atoi(argv[3]);
    }
    if (argc >= 5) cfg.TIME_LIMIT_SEC = std::atof(argv[4]);
    if (argc >= 6) cfg.THREADS = std::atoi(argv[5]);

    std::cout << "Starting search: N=" << cfg.N
              << " alpha<=" << cfg.MAX_ALPHA
              << " edges<=" << cfg.MAX_EDGES
              << " max_e(7)<=" << cfg.MAX_SUB_EDGES
              << " threads=" << cfg.THREADS
              << " time=" << cfg.TIME_LIMIT_SEC << "s\n" << std::flush;

    std::atomic<bool> found{false};
    std::atomic<long long> total_steps{0};
    std::atomic<int> global_best{1000000000};
    std::mutex print_mtx;
    Graph best_graph;
    EvalResult best_eval{};

    auto t0 = std::chrono::steady_clock::now();

    auto worker = [&](int tid) {
        std::mt19937_64 rng(0x9e3779b97f4a7c15ULL * (tid + 1) ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());
        int restart = 0;
        const int IND_CAP = 5000;
        const int DENSE_CAP = 5000;

        while (!found.load(std::memory_order_relaxed)) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t0).count();
            if (elapsed >= cfg.TIME_LIMIT_SEC) break;

            int mode = (tid + restart) % 4;
            restart++;
            Graph g;
            init_graph(g, cfg, mode, rng);

            // Adaptive weights
            double w_ind = 1.0 + 0.5 * (tid % 4);
            double w_dense = 1.0 + 0.5 * ((tid / 4) % 4);

            EvalResult cur = evaluate(g, cfg, IND_CAP, DENSE_CAP, rng);
            auto score_fn = [&](const EvalResult &r) -> double {
                return w_ind * r.ind_cnt + w_dense * (r.dense_cnt + 0.5 * r.dense_excess);
            };
            double cur_score = score_fn(cur);
            int cur_total = cur.ind_cnt + cur.dense_cnt;

            double temp = 8.0;
            const double cool = 0.9997;
            int stale = 0;
            int local_best = cur_total;

            for (int step = 0; step < 30000 && !found.load(std::memory_order_relaxed); ++step) {
                if ((step & 1023) == 0) {
                    total_steps.fetch_add(1024, std::memory_order_relaxed);
                    double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                    if (el >= cfg.TIME_LIMIT_SEC) break;
                }

                if (cur_total == 0) {
                    if (verify_exact(g, cfg)) {
                        if (!found.exchange(true)) {
                            std::lock_guard<std::mutex> lk(print_mtx);
                            print_graph(g);
                        }
                        return;
                    }
                }

                if (cur_total < global_best.load(std::memory_order_relaxed)) {
                    std::lock_guard<std::mutex> lk(print_mtx);
                    if (cur_total < global_best.load()) {
                        global_best.store(cur_total);
                        best_graph = g;
                        best_eval = cur;
                        double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                        std::cout << "[" << el << "s tid=" << tid << " mode=" << mode
                                  << "] NEW BEST total=" << cur_total
                                  << " (ind=" << cur.ind_cnt
                                  << ", dense=" << cur.dense_cnt
                                  << ", dense_ex=" << cur.dense_excess
                                  << ", E=" << g.edges << ")\n" << std::flush;
                    }
                }

                // Propose a move: usually an edge swap (remove one edge, add one non-edge)
                // keeping E == MAX_EDGES, or occasionally +/- 1 edge if E < MAX_EDGES.
                int ru = -1, rv = -1; // edge to remove
                int au = -1, av = -1; // edge to add

                // Choose edge to REMOVE: bias toward edges inside sample_dense if dense_cnt > 0
                if (cur.dense_cnt > 0 && cur.sample_dense != 0 && (rng() % 100) < 75) {
                    int verts[7], vc = 0;
                    uint64_t m = cur.sample_dense;
                    while (m) { verts[vc++] = ctz(m); m &= m - 1; }
                    for (int tries = 0; tries < 20; ++tries) {
                        int a = verts[rng() % vc];
                        int b = verts[rng() % vc];
                        if (a != b && g.has_edge(a, b)) { ru = a; rv = b; break; }
                    }
                }
                if (ru == -1) {
                    // random existing edge
                    for (int tries = 0; tries < 30; ++tries) {
                        int u = rng() % cfg.N;
                        if (g.deg[u] == 0) continue;
                        int k = rng() % g.deg[u];
                        uint64_t m = g.adj[u];
                        int v = -1;
                        while (k-- >= 0) { v = ctz(m); m &= m - 1; }
                        ru = u; rv = v;
                        break;
                    }
                }

                // Choose non-edge to ADD: bias toward non-edges inside sample_ind if ind_cnt > 0
                if (cur.ind_cnt > 0 && cur.sample_ind != 0 && (rng() % 100) < 75) {
                    int verts[8], vc = 0;
                    uint64_t m = cur.sample_ind;
                    while (m) { verts[vc++] = ctz(m); m &= m - 1; }
                    for (int tries = 0; tries < 20; ++tries) {
                        int a = verts[rng() % vc];
                        int b = verts[rng() % vc];
                        if (a != b && !g.has_edge(a, b)) { au = a; av = b; break; }
                    }
                }
                if (au == -1) {
                    for (int tries = 0; tries < 30; ++tries) {
                        int a = rng() % cfg.N;
                        int b = rng() % cfg.N;
                        if (a != b && !g.has_edge(a, b) && !((a == ru && b == rv) || (a == rv && b == ru))) {
                            au = a; av = b;
                            break;
                        }
                    }
                }
                if (ru == -1 || au == -1) continue;

                // Sometimes only remove (if dense_cnt > 0 and ind_cnt == 0), or only add (if g.edges < cfg.MAX_EDGES)
                int move_type = 0; // 0: swap, 1: only remove, 2: only add
                if (cur.ind_cnt == 0 && cur.dense_cnt > 0 && (rng() % 100) < 25) {
                    move_type = 1;
                } else if (g.edges < cfg.MAX_EDGES && cur.ind_cnt > 0 && (rng() % 100) < 60) {
                    move_type = 2;
                }

                if (move_type == 0) {
                    g.remove_edge(ru, rv);
                    g.add_edge(au, av);
                } else if (move_type == 1) {
                    g.remove_edge(ru, rv);
                } else {
                    g.add_edge(au, av);
                }

                EvalResult nxt = evaluate(g, cfg, IND_CAP, DENSE_CAP, rng);
                double nxt_score = score_fn(nxt);
                double delta = nxt_score - cur_score;

                bool accept = (delta <= 0.0);
                if (!accept && temp > 1e-4) {
                    double prob = std::exp(-delta / temp);
                    double u01 = (double)(rng() >> 11) * (1.0 / (double)(1ULL << 53));
                    accept = (u01 < prob);
                }

                if (accept) {
                    cur = nxt;
                    cur_score = nxt_score;
                    cur_total = cur.ind_cnt + cur.dense_cnt;
                    if (cur_total < local_best) {
                        local_best = cur_total;
                        stale = 0;
                    } else {
                        stale++;
                    }
                } else {
                    // Revert
                    if (move_type == 0) {
                        g.remove_edge(au, av);
                        g.add_edge(ru, rv);
                    } else if (move_type == 1) {
                        g.add_edge(ru, rv);
                    } else {
                        g.remove_edge(au, av);
                    }
                    stale++;
                }

                temp *= cool;
                if (temp < 0.05) temp = 0.05;

                // Adaptive reweight if stuck on one constraint
                if ((step & 511) == 511 && stale > 400) {
                    if (cur.ind_cnt > 0 && cur.dense_cnt == 0) w_ind = std::min(10.0, w_ind * 1.25);
                    else if (cur.dense_cnt > 0 && cur.ind_cnt == 0) w_dense = std::min(10.0, w_dense * 1.25);
                    cur_score = score_fn(cur);
                }

                if (stale > 4000) break; // restart
            }
        }
    };

    std::vector<std::thread> pool;
    for (int t = 0; t < cfg.THREADS; ++t) pool.emplace_back(worker, t);
    for (auto &th : pool) th.join();

    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "Done in " << elapsed << "s, total_steps=" << total_steps.load()
              << ", found=" << (found.load() ? "YES" : "NO")
              << ", global_best=" << global_best.load() << "\n";
    if (!found.load() && global_best.load() < 1000000000) {
        std::cout << "Best near-miss had ind=" << best_eval.ind_cnt
                  << " dense=" << best_eval.dense_cnt
                  << " dense_ex=" << best_eval.dense_excess
                  << " E=" << best_graph.edges << "\n";
        // Print degree sequence of best near-miss
        std::vector<int> degs(best_graph.deg, best_graph.deg + best_graph.n);
        std::sort(degs.begin(), degs.end());
        std::cout << "Best deg seq:";
        for (int d : degs) std::cout << " " << d;
        std::cout << "\n";
    }
    return 0;
}
