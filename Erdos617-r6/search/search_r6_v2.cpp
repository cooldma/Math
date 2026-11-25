#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <random>
#include <thread>
#include <vector>

// Exact incremental local search for Erdos #617 single-graph relaxation at r = 6:
// Find G on N vertices (default N=37) with:
//   e(G) <= MAX_EDGES (default 111)
//   alpha(G) <= MAX_ALPHA (default 6)
//   max_{|S|=7} e(G[S]) <= 16

static inline int popcnt(uint64_t x) { return __builtin_popcountll(x); }
static inline int ctz(uint64_t x) { return __builtin_ctzll(x); }

struct Graph {
    int n;
    uint64_t adj[64];
    uint64_t non_adj[64];
    uint64_t all_mask;
    int deg[64];
    int edges;

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
    inline bool has_edge(int u, int v) const { return (adj[u] >> v) & 1ULL; }
    inline void add_edge(int u, int v) {
        adj[u] |= (1ULL << v); adj[v] |= (1ULL << u);
        non_adj[u] &= ~(1ULL << v); non_adj[v] &= ~(1ULL << u);
        deg[u]++; deg[v]++; edges++;
    }
    inline void remove_edge(int u, int v) {
        adj[u] &= ~(1ULL << v); adj[v] &= ~(1ULL << u);
        non_adj[u] |= (1ULL << v); non_adj[v] |= (1ULL << u);
        deg[u]--; deg[v]--; edges--;
    }
};

// Fast exact count of independent sets of size `rem` inside `cand` (NO CAP).
int64_t count_is(const Graph &g, int rem, uint64_t cand) {
    int pc = popcnt(cand);
    if (pc < rem) return 0;
    if (rem == 0) return 1;
    if (rem == 1) return pc;
    if (rem == 2) {
        int64_t tot = 0;
        while (cand) {
            int u = ctz(cand);
            cand &= cand - 1;
            tot += popcnt(cand & g.non_adj[u]);
        }
        return tot;
    }
    if (rem == 3) {
        int64_t tot = 0;
        while (cand) {
            int u = ctz(cand);
            cand &= cand - 1;
            uint64_t c1 = cand & g.non_adj[u];
            if (popcnt(c1) < 2) continue;
            while (c1) {
                int v = ctz(c1);
                c1 &= c1 - 1;
                tot += popcnt(c1 & g.non_adj[v]);
            }
        }
        return tot;
    }
    int64_t tot = 0;
    while (cand) {
        if (popcnt(cand) < rem) break;
        int u = ctz(cand);
        cand &= cand - 1;
        tot += count_is(g, rem - 1, cand & g.non_adj[u]);
    }
    return tot;
}

// Find one random/first independent set of size `rem` in `cand` (for targeted moves).
bool find_one_is(const Graph &g, int rem, uint64_t cand, uint64_t &out_mask, std::mt19937_64 &rng) {
    int pc = popcnt(cand);
    if (pc < rem) return false;
    if (rem == 0) { out_mask = 0; return true; }
    // collect vertices and shuffle slightly at top levels
    int vs[64], vc = 0;
    uint64_t t = cand;
    while (t) { vs[vc++] = ctz(t); t &= t - 1; }
    if (rem >= 4) {
        for (int i = vc - 1; i > 0; --i) std::swap(vs[i], vs[rng() % (i + 1)]);
    }
    uint64_t rem_mask = cand;
    for (int i = 0; i < vc; ++i) {
        int u = vs[i];
        rem_mask &= ~(1ULL << u);
        if (popcnt(rem_mask) < rem - 1) return false;
        uint64_t sub = 0;
        if (find_one_is(g, rem - 1, rem_mask & g.non_adj[u], sub, rng)) {
            out_mask = sub | (1ULL << u);
            return true;
        }
    }
    return false;
}

// Full exact count of 7-subsets with >= 17 edges.
void full_count_dense7(const Graph &g, int64_t &dense_cnt, int64_t &dense_excess) {
    dense_cnt = 0;
    dense_excess = 0;
    int nbrs[64];
    for (int u = 0; u < g.n; ++u) {
        if (g.deg[u] < 5) continue;
        int d = 0;
        uint64_t tmp = g.adj[u];
        while (tmp) { nbrs[d++] = ctz(tmp); tmp &= tmp - 1; }
        // Case 1: d_S(u) == 6
        if (d >= 6) {
            for (int i0 = 0; i0 < d - 5; ++i0) {
                int v0 = nbrs[i0]; uint64_t a0 = g.adj[v0];
                for (int i1 = i0 + 1; i1 < d - 4; ++i1) {
                    int v1 = nbrs[i1]; int e01 = (a0 >> v1) & 1; uint64_t a1 = g.adj[v1];
                    for (int i2 = i1 + 1; i2 < d - 3; ++i2) {
                        int v2 = nbrs[i2]; int e012 = e01 + ((a0 >> v2) & 1) + ((a1 >> v2) & 1); uint64_t a2 = g.adj[v2];
                        for (int i3 = i2 + 1; i3 < d - 2; ++i3) {
                            int v3 = nbrs[i3]; int e0123 = e012 + ((a0 >> v3) & 1) + ((a1 >> v3) & 1) + ((a2 >> v3) & 1);
                            if (e0123 + 9 < 11) continue;
                            uint64_t a3 = g.adj[v3];
                            for (int i4 = i3 + 1; i4 < d - 1; ++i4) {
                                int v4 = nbrs[i4]; int e01234 = e0123 + ((a0 >> v4) & 1) + ((a1 >> v4) & 1) + ((a2 >> v4) & 1) + ((a3 >> v4) & 1);
                                if (e01234 + 5 < 11) continue;
                                uint64_t a4 = g.adj[v4];
                                for (int i5 = i4 + 1; i5 < d; ++i5) {
                                    int v5 = nbrs[i5];
                                    int eA = e01234 + ((a0 >> v5) & 1) + ((a1 >> v5) & 1) + ((a2 >> v5) & 1) + ((a3 >> v5) & 1) + ((a4 >> v5) & 1);
                                    if (eA < 11) continue;
                                    uint64_t maskA = (1ULL<<v0)|(1ULL<<v1)|(1ULL<<v2)|(1ULL<<v3)|(1ULL<<v4)|(1ULL<<v5);
                                    int vs[6] = {v0,v1,v2,v3,v4,v5};
                                    bool canon = true;
                                    for (int k = 0; k < 6; ++k)
                                        if (vs[k] < u && popcnt(g.adj[vs[k]] & maskA) == 5) { canon = false; break; }
                                    if (!canon) continue;
                                    dense_cnt++;
                                    dense_excess += (6 + eA - 16);
                                }
                            }
                        }
                    }
                }
            }
        }
        // Case 2: max deg in S == 5, attained at u
        uint64_t non_u = g.non_adj[u];
        for (int i0 = 0; i0 < d - 4; ++i0) {
            int v0 = nbrs[i0]; uint64_t a0 = g.adj[v0];
            for (int i1 = i0 + 1; i1 < d - 3; ++i1) {
                int v1 = nbrs[i1]; int e01 = (a0 >> v1) & 1; uint64_t a1 = g.adj[v1];
                for (int i2 = i1 + 1; i2 < d - 2; ++i2) {
                    int v2 = nbrs[i2]; int e012 = e01 + ((a0 >> v2) & 1) + ((a1 >> v2) & 1);
                    if (e012 + 7 < 7) continue;
                    uint64_t a2 = g.adj[v2];
                    for (int i3 = i2 + 1; i3 < d - 1; ++i3) {
                        int v3 = nbrs[i3]; int e0123 = e012 + ((a0 >> v3) & 1) + ((a1 >> v3) & 1) + ((a2 >> v3) & 1);
                        if (e0123 + 4 < 7) continue;
                        uint64_t a3 = g.adj[v3];
                        for (int i4 = i3 + 1; i4 < d; ++i4) {
                            int v4 = nbrs[i4];
                            int eA = e0123 + ((a0 >> v4) & 1) + ((a1 >> v4) & 1) + ((a2 >> v4) & 1) + ((a3 >> v4) & 1);
                            if (eA < 7) continue;
                            uint64_t a4 = g.adj[v4];
                            int needW = 12 - eA;
                            uint64_t maskA = (1ULL<<v0)|(1ULL<<v1)|(1ULL<<v2)|(1ULL<<v3)|(1ULL<<v4);
                            uint64_t cands = non_u & (a0 | a1 | a2 | a3 | a4);
                            int dA[5] = {popcnt(a0&maskA), popcnt(a1&maskA), popcnt(a2&maskA), popcnt(a3&maskA), popcnt(a4&maskA)};
                            int vs[5] = {v0,v1,v2,v3,v4};
                            while (cands) {
                                int w = ctz(cands); cands &= cands - 1;
                                int dw = popcnt(g.adj[w] & maskA);
                                if (dw < needW) continue;
                                if (dw == 5 && w < u) continue;
                                bool ok = true;
                                for (int k = 0; k < 5; ++k) {
                                    int dv = 1 + dA[k] + (int)((g.adj[w] >> vs[k]) & 1ULL);
                                    if (dv == 6 || (dv == 5 && vs[k] < u)) { ok = false; break; }
                                }
                                if (!ok) continue;
                                dense_cnt++;
                                dense_excess += (5 + eA + dw - 16);
                            }
                        }
                    }
                }
            }
        }
    }
}

// Incremental dense7 count for pair (u, v):
// Counts 5-subsets A of V \ {u, v} with d_A(u) + d_A(v) + e(A) >= 16.
// Returns {cnt_eq16, cnt_ge16} (which are |delta_dense_cnt| and |delta_dense_excess|!).
struct PairDense {
    int64_t eq16;
    int64_t ge16;
};

PairDense count_pair_dense(const Graph &g, int u, int v) {
    uint64_t uv_mask = (1ULL << u) | (1ULL << v);
    uint64_t nu = g.adj[u] & ~uv_mask;
    uint64_t nv = g.adj[v] & ~uv_mask;
    uint64_t p2 = nu & nv;
    if (!p2) return {0, 0}; // max d_A(u)+d_A(v) <= 5 => max score <= 15 < 16!

    uint64_t p1 = (nu ^ nv);
    uint64_t p0 = g.all_mask & ~uv_mask & ~(p2 | p1);

    // Order vertices: p2 (w=2), p1 (w=1), p0 (w=0)
    int verts[64], w[64], m = 0;
    int pos_of[64];
    uint64_t t = p2;
    while (t) { int x = ctz(t); t &= t - 1; pos_of[x] = m; verts[m] = x; w[m++] = 2; }
    int n2 = m;
    t = p1;
    while (t) { int x = ctz(t); t &= t - 1; pos_of[x] = m; verts[m] = x; w[m++] = 1; }
    int n21 = m;
    t = p0;
    while (t) { int x = ctz(t); t &= t - 1; pos_of[x] = m; verts[m] = x; w[m++] = 0; }

    // prefix sums of weights for fast upper bound on remaining weight
    int pref[65];
    pref[0] = 0;
    for (int i = 0; i < m; ++i) pref[i + 1] = pref[i] + w[i];

    // Precompute suffix masks of vertices with index >= idx
    uint64_t suf_mask[65];
    suf_mask[m] = 0;
    for (int i = m - 1; i >= 0; --i) suf_mask[i] = suf_mask[i + 1] | (1ULL << verts[i]);

    PairDense res{0, 0};

    // Since w is sorted decreasingly, first chosen vertex i0 MUST have i0 < n2
    // (because at least one vertex of A must be in p2!).
    for (int i0 = 0; i0 < n2 && i0 <= m - 5; ++i0) {
        // Max possible weight of 5 vertices starting at i0:
        if (pref[i0 + 5] - pref[i0] < 6) break;
        int x0 = verts[i0]; int w0 = w[i0]; uint64_t a0 = g.adj[x0];
        for (int i1 = i0 + 1; i1 <= m - 4; ++i1) {
            int w01 = w0 + w[i1];
            if (w01 + pref[i1 + 4] - pref[i1 + 1] < 6) break;
            int x1 = verts[i1]; uint64_t a1 = g.adj[x1];
            int e01 = (a0 >> x1) & 1;
            // Max total edges with e01 fixed: e01 + 9
            if (w01 + pref[i1 + 4] - pref[i1 + 1] + e01 + 9 < 16) continue;
            for (int i2 = i1 + 1; i2 <= m - 3; ++i2) {
                int w012 = w01 + w[i2];
                if (w012 + pref[i2 + 3] - pref[i2 + 1] < 6) break;
                int x2 = verts[i2]; uint64_t a2 = g.adj[x2];
                int e012 = e01 + ((a0 >> x2) & 1) + ((a1 >> x2) & 1);
                if (w012 + pref[i2 + 3] - pref[i2 + 1] + e012 + 7 < 16) continue;
                for (int i3 = i2 + 1; i3 <= m - 2; ++i3) {
                    int w0123 = w012 + w[i3];
                    int max_w4 = w[i3 + 1];
                    if (w0123 + max_w4 < 6) break;
                    int x3 = verts[i3]; uint64_t a3 = g.adj[x3];
                    int e0123 = e012 + ((a0 >> x3) & 1) + ((a1 >> x3) & 1) + ((a2 >> x3) & 1);
                    int s4 = w0123 + e0123;
                    if (s4 + max_w4 + 4 < 16) continue;
                    int need = 16 - s4; // >= 2 always (since max s4 = 8+6 = 14)
                    uint64_t mask4 = (1ULL<<x0)|(1ULL<<x1)|(1ULL<<x2)|(1ULL<<x3);
                    // Candidate 5th vertices with index >= i3+1:
                    // Must have w[x4] + popcnt(adj[x4] & mask4) >= need
                    uint64_t cands = suf_mask[i3 + 1] & (a0 | a1 | a2 | a3 | (need <= 2 ? p2 : 0ULL));
                    while (cands) {
                        int x4 = ctz(cands);
                        cands &= cands - 1;
                        int wx4 = ((p2 >> x4) & 1ULL) ? 2 : (((p1 >> x4) & 1ULL) ? 1 : 0);
                        int deg4 = popcnt(g.adj[x4] & mask4);
                        int tot = s4 + wx4 + deg4;
                        if (tot >= 16) {
                            res.ge16++;
                            if (tot == 16) res.eq16++;
                        }
                    }
                }
            }
        }
    }
    return res;
}

void self_test() {
    std::mt19937_64 rng(777);
    Graph g;
    int N = 20, K = 4;
    g.init(N);
    for (int i = 0; i < N; ++i)
        for (int j = i + 1; j < N; ++j)
            if ((rng() % 100) < 40) g.add_edge(i, j);

    int64_t ind = count_is(g, K + 1, g.all_mask);
    int64_t dcnt = 0, dex = 0;
    full_count_dense7(g, dcnt, dex);

    for (int step = 0; step < 100; ++step) {
        int u = rng() % N, v = rng() % N;
        if (u == v) continue;
        bool had = g.has_edge(u, v);
        int64_t di = count_is(g, K - 1, g.non_adj[u] & g.non_adj[v]);
        PairDense pd = count_pair_dense(g, u, v);
        if (had) {
            g.remove_edge(u, v);
            ind += di;
            dcnt -= pd.eq16;
            dex -= pd.ge16;
        } else {
            g.add_edge(u, v);
            ind -= di;
            dcnt += pd.eq16;
            dex += pd.ge16;
        }
        int64_t true_ind = count_is(g, K + 1, g.all_mask);
        int64_t true_dcnt = 0, true_dex = 0;
        full_count_dense7(g, true_dcnt, true_dex);
        if (ind != true_ind || dcnt != true_dcnt || dex != true_dex) {
            std::cerr << "INCREMENTAL SELF TEST FAILED at step " << step
                      << " ind=" << ind << "/" << true_ind
                      << " dcnt=" << dcnt << "/" << true_dcnt
                      << " dex=" << dex << "/" << true_dex << "\n";
            std::exit(1);
        }
    }
    std::cout << "[self_test] Incremental ind + dense7 PASSED (100 random flips)\n" << std::flush;
}

void print_graph(const Graph &g) {
    std::cout << "=== WITNESS FOUND: N=" << g.n << " E=" << g.edges << " ===\n";
    std::cout << "EDGES=[";
    bool first = true;
    for (int u = 0; u < g.n; ++u)
        for (int v = u + 1; v < g.n; ++v)
            if (g.has_edge(u, v)) {
                if (!first) std::cout << ",";
                std::cout << "(" << u << "," << v << ")";
                first = false;
            }
    std::cout << "]\n" << std::flush;
}

int main(int argc, char **argv) {
    self_test();
    int N = (argc >= 2) ? std::atoi(argv[1]) : 37;
    int MAX_ALPHA = (argc >= 3) ? std::atoi(argv[2]) : 6;
    int MAX_EDGES = (argc >= 4) ? std::atoi(argv[3]) : 111;
    double TIME_LIM = (argc >= 5) ? std::atof(argv[4]) : 45.0;
    int THREADS = (argc >= 6) ? std::atoi(argv[5]) : 20;
    int HARD_DENSE = (argc >= 7) ? std::atoi(argv[6]) : 0; // 1: forbid dense > 0

    std::cout << "Incremental v2 search: N=" << N << " alpha<=" << MAX_ALPHA
              << " E<=" << MAX_EDGES << " max_e(7)<=16 threads=" << THREADS
              << " time=" << TIME_LIM << "s hard_dense=" << HARD_DENSE << "\n" << std::flush;

    std::atomic<bool> found{false};
    std::atomic<int64_t> global_best{1000000000000LL};
    std::atomic<int64_t> total_steps{0};
    std::mutex mtx;
    auto t0 = std::chrono::steady_clock::now();

    auto worker = [&](int tid) {
        std::mt19937_64 rng(0x9e3779b97f4a7c15ULL * (tid + 1) ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());
        int restart = 0;
        while (!found.load(std::memory_order_relaxed)) {
            double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            if (el >= TIME_LIM) break;

            int mode = (tid + restart) % 4;
            restart++;
            Graph g;
            g.init(N);

            if (HARD_DENSE) {
                // Start strictly with dense == 0!
                if (mode == 0) {
                    // 6 disjoint K_6 + 1 vertex connected to 1 vertex in each K_6, then greedily add edges keeping dense==0
                    int k_clq = std::min(6, N / 6);
                    for (int c = 0; c < k_clq; ++c)
                        for (int i = 6*c; i < 6*c+6; ++i)
                            for (int j = i+1; j < 6*c+6; ++j) g.add_edge(i, j);
                    if (N == 37) {
                        for (int c = 0; c < 6; ++c) g.add_edge(36, 6*c);
                    }
                } else {
                    // Greedy K4-free graph (guaranteed dense == 0!)
                    std::vector<std::pair<int,int>> es;
                    for (int i = 0; i < N; ++i)
                        for (int j = i + 1; j < N; ++j) es.push_back({i, j});
                    std::shuffle(es.begin(), es.end(), rng);
                    for (auto [u, v] : es) {
                        if (g.edges >= MAX_EDGES) break;
                        uint64_t cn = g.adj[u] & g.adj[v];
                        bool mk4 = false;
                        uint64_t t = cn;
                        while (t) { int x = ctz(t); t &= t - 1; if (g.adj[x] & cn) { mk4 = true; break; } }
                        if (!mk4) g.add_edge(u, v);
                    }
                }
                // Fill remaining edges keeping dense == 0
                for (int tries = 0; tries < 5000 && g.edges < MAX_EDGES; ++tries) {
                    int u = rng() % N, v = rng() % N;
                    if (u != v && !g.has_edge(u, v)) {
                        PairDense pd = count_pair_dense(g, u, v);
                        if (pd.eq16 == 0 && pd.ge16 == 0) g.add_edge(u, v);
                    }
                }
            } else if (mode == 0) {
                // Random graph with MAX_EDGES
                std::vector<std::pair<int,int>> es;
                for (int i = 0; i < N; ++i)
                    for (int j = i + 1; j < N; ++j) es.push_back({i, j});
                std::shuffle(es.begin(), es.end(), rng);
                for (int k = 0; k < MAX_EDGES; ++k) g.add_edge(es[k].first, es[k].second);
            } else if (mode == 1) {
                // Greedy K4-free graph up to MAX_EDGES
                std::vector<std::pair<int,int>> es;
                for (int i = 0; i < N; ++i)
                    for (int j = i + 1; j < N; ++j) es.push_back({i, j});
                std::shuffle(es.begin(), es.end(), rng);
                for (auto [u, v] : es) {
                    if (g.edges >= MAX_EDGES) break;
                    uint64_t cn = g.adj[u] & g.adj[v];
                    bool mk4 = false;
                    uint64_t t = cn;
                    while (t) { int x = ctz(t); t &= t - 1; if (g.adj[x] & cn) { mk4 = true; break; } }
                    if (!mk4) g.add_edge(u, v);
                }
                while (g.edges < MAX_EDGES) {
                    int u = rng() % N, v = rng() % N;
                    if (u != v && !g.has_edge(u, v)) g.add_edge(u, v);
                }
            } else if (mode == 2) {
                // Random 6-regular-ish (degree balanced)
                for (int iter = 0; iter < 50000 && g.edges < MAX_EDGES; ++iter) {
                    int u = rng() % N, v = rng() % N;
                    if (u != v && !g.has_edge(u, v) && g.deg[u] < 6 && g.deg[v] < 6) g.add_edge(u, v);
                }
                while (g.edges < MAX_EDGES) {
                    int u = rng() % N, v = rng() % N;
                    if (u != v && !g.has_edge(u, v)) g.add_edge(u, v);
                }
            } else {
                // Perturbed cliques: MAX_ALPHA cliques, break largest clique
                for (int i = 0; i < N; ++i)
                    for (int j = i + 1; j < N; ++j)
                        if (i % MAX_ALPHA == j % MAX_ALPHA) g.add_edge(i, j);
                // remove 10 random edges, add random edges to MAX_EDGES
                for (int k = 0; k < 10; ++k) {
                    int u = rng() % N;
                    if (g.deg[u] == 0) continue;
                    int v = ctz(g.adj[u]);
                    g.remove_edge(u, v);
                }
                while (g.edges < MAX_EDGES) {
                    int u = rng() % N, v = rng() % N;
                    if (u != v && !g.has_edge(u, v)) g.add_edge(u, v);
                }
            }

            int64_t ind = count_is(g, MAX_ALPHA + 1, g.all_mask);
            int64_t dcnt = 0, dex = 0;
            full_count_dense7(g, dcnt, dex);

            // Some threads optimize log-energy when ind is huge, then linear when small!
            bool k4_free_mode = (tid >= 15);
            double w_ind = 1.0 + 0.5 * (tid % 3);
            double w_dense = 2.0 + 1.0 * ((tid / 3) % 4);
            auto energy = [&](int64_t i_c, int64_t d_c, int64_t d_e) -> double {
                double e_ind = (i_c > 50) ? (50.0 + 30.0 * std::log((double)i_c / 50.0)) : (double)i_c;
                double e_den = (d_c > 50) ? (50.0 + 30.0 * std::log((double)d_c / 50.0)) : (double)(d_c + 0.5 * d_e);
                return w_ind * e_ind + w_dense * e_den;
            };
            double cur_E = energy(ind, dcnt, dex);
            double temp = 4.0;
            int stale = 0;
            int64_t local_best = ind + dcnt;

            for (int step = 0; step < 300000 && !found.load(std::memory_order_relaxed); ++step) {
                if ((step & 4095) == 0) {
                    total_steps.fetch_add(4096, std::memory_order_relaxed);
                    if (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() >= TIME_LIM) break;
                }

                int64_t tot_v = ind + dcnt;
                if (tot_v == 0) {
                    // Double check exact from scratch!
                    int64_t ci = count_is(g, MAX_ALPHA + 1, g.all_mask);
                    int64_t cd = 0, ce = 0;
                    full_count_dense7(g, cd, ce);
                    if (ci == 0 && cd == 0 && g.edges <= MAX_EDGES) {
                        if (!found.exchange(true)) {
                            std::lock_guard<std::mutex> lk(mtx);
                            print_graph(g);
                        }
                        return;
                    }
                }

                if (tot_v < global_best.load(std::memory_order_relaxed)) {
                    std::lock_guard<std::mutex> lk(mtx);
                    if (tot_v < global_best.load()) {
                        global_best.store(tot_v);
                        double el2 = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                        std::cout << "[" << el2 << "s tid=" << tid << " mode=" << mode
                                  << (k4_free_mode ? " K4F" : "")
                                  << "] NEW BEST tot=" << tot_v
                                  << " (ind=" << ind << ", dense=" << dcnt
                                  << ", dex=" << dex << ", E=" << g.edges << ")\n" << std::flush;
                    }
                }

                // Choose swap: remove existing edge (ru, rv), add non-edge (au, av)
                int ru = -1, rv = -1;
                for (int tr = 0; tr < 20; ++tr) {
                    int u = rng() % N;
                    if (g.deg[u] == 0) continue;
                    int k = rng() % g.deg[u];
                    uint64_t m = g.adj[u];
                    int v = -1;
                    while (k-- >= 0) { v = ctz(m); m &= m - 1; }
                    ru = u; rv = v; break;
                }
                int au = -1, av = -1;
                if (ind > 0 && (step & 7) == 0) {
                    // Occasionally target an actual violating IS!
                    uint64_t is_m = 0;
                    if (find_one_is(g, MAX_ALPHA + 1, g.all_mask, is_m, rng)) {
                        int vs[16], vc = 0;
                        while (is_m) { vs[vc++] = ctz(is_m); is_m &= is_m - 1; }
                        int a = vs[rng() % vc], b = vs[rng() % vc];
                        if (a != b && !g.has_edge(a, b)) { au = a; av = b; }
                    }
                }
                if (au == -1) {
                    for (int tr = 0; tr < 20; ++tr) {
                        int a = rng() % N, b = rng() % N;
                        if (a != b && !g.has_edge(a, b)) { au = a; av = b; break; }
                    }
                }
                if (ru == -1 || au == -1) continue;

                // Evaluate removing (ru, rv)
                int64_t di_rem = count_is(g, MAX_ALPHA - 1, g.non_adj[ru] & g.non_adj[rv]);
                PairDense pd_rem = count_pair_dense(g, ru, rv);
                g.remove_edge(ru, rv);

                // If k4_free_mode, reject adding (au, av) if it creates a K4!
                if (k4_free_mode) {
                    uint64_t cn = g.adj[au] & g.adj[av];
                    bool mk4 = false;
                    uint64_t t = cn;
                    while (t) { int x = ctz(t); t &= t - 1; if (g.adj[x] & cn) { mk4 = true; break; } }
                    if (mk4) {
                        g.add_edge(ru, rv);
                        continue;
                    }
                }

                // Evaluate adding (au, av)
                int64_t di_add = count_is(g, MAX_ALPHA - 1, g.non_adj[au] & g.non_adj[av]);
                PairDense pd_add = count_pair_dense(g, au, av);

                int64_t nxt_ind = ind + di_rem - di_add;
                int64_t nxt_dcnt = dcnt - pd_rem.eq16 + pd_add.eq16;
                int64_t nxt_dex = dex - pd_rem.ge16 + pd_add.ge16;
                if (HARD_DENSE && nxt_dcnt > 0) {
                    g.add_edge(ru, rv);
                    continue;
                }
                double nxt_E = energy(nxt_ind, nxt_dcnt, nxt_dex);
                double delta = nxt_E - cur_E;

                bool acc = (delta <= 0.0);
                if (!acc && temp > 1e-4) {
                    double u01 = (double)(rng() >> 11) * (1.0 / (double)(1ULL << 53));
                    acc = (u01 < std::exp(-delta / temp));
                }

                if (acc) {
                    g.add_edge(au, av);
                    ind = nxt_ind; dcnt = nxt_dcnt; dex = nxt_dex; cur_E = nxt_E;
                    if (ind + dcnt < local_best) { local_best = ind + dcnt; stale = 0; }
                    else stale++;
                } else {
                    g.add_edge(ru, rv);
                    stale++;
                }

                temp *= 0.99995;
                if (temp < 0.05) temp = 0.05;
                if (stale > 40000) break;
            }
        }
    };

    std::vector<std::thread> pool;
    for (int t = 0; t < THREADS; ++t) pool.emplace_back(worker, t);
    for (auto &th : pool) th.join();

    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "Done in " << elapsed << "s, total_steps=" << total_steps.load()
              << ", found=" << (found.load() ? "YES" : "NO")
              << ", global_best=" << global_best.load() << "\n";
    return 0;
}
