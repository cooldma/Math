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

// Fast search for triangle-free graph F on n = 2r+1 vertices with:
//   e(F) >= ceil(r*(r+3)/2)
//   min_{|S|=r+1} e(F[S]) >= r - 1
// Runs exact subset scan using bitmasks (C(13,7)=1716, C(17,9)=24310).

static inline int popcnt(uint32_t x) { return __builtin_popcount(x); }
static inline int ctz(uint32_t x) { return __builtin_ctz(x); }

int N, R, NEED_E, NEED_MIN;
std::vector<uint32_t> subsets;

void gen_subsets(int idx, int left, uint32_t mask) {
    if (left == 0) { subsets.push_back(mask); return; }
    if (N - idx < left) return;
    gen_subsets(idx + 1, left - 1, mask | (1u << idx));
    gen_subsets(idx + 1, left, mask);
}

struct Eval {
    int min_e;
    int bad_cnt;
    int bad_deficit;
    uint32_t sample_bad;
};

Eval eval_graph(const uint32_t *adj, std::mt19937_64 &rng) {
    Eval res{1000000, 0, 0, 0};
    for (uint32_t m : subsets) {
        int e2 = 0;
        uint32_t t = m;
        while (t) {
            int u = ctz(t);
            t &= t - 1;
            e2 += popcnt(adj[u] & m);
        }
        int e = e2 >> 1;
        if (e < res.min_e) res.min_e = e;
        if (e < NEED_MIN) {
            res.bad_cnt++;
            res.bad_deficit += (NEED_MIN - e);
            if (res.bad_cnt == 1 || (rng() % res.bad_cnt == 0)) res.sample_bad = m;
        }
    }
    return res;
}

int main(int argc, char **argv) {
    R = (argc >= 2) ? std::atoi(argv[1]) : 6;
    double time_lim = (argc >= 3) ? std::atof(argv[2]) : 10.0;
    N = 2 * R + 1;
    NEED_E = (R * (R + 3) + 1) / 2;
    NEED_MIN = R - 1;
    gen_subsets(0, R + 1, 0);
    std::cout << "TF search: r=" << R << " n=" << N << " need_e>=" << NEED_E
              << " need_min>=" << NEED_MIN << " subsets=" << subsets.size() << "\n" << std::flush;

    std::atomic<bool> found{false};
    std::atomic<int> best_bad{1000000000};
    std::mutex mtx;
    auto t0 = std::chrono::steady_clock::now();

    auto worker = [&](int tid) {
        std::mt19937_64 rng(0x123456789abcdefULL * (tid + 1) ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());
        while (!found.load()) {
            double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            if (el >= time_lim) break;

            uint32_t adj[32] = {0};
            int edges = 0;
            // Random maximal triangle-free graph
            std::vector<std::pair<int,int>> pairs;
            for (int i = 0; i < N; ++i)
                for (int j = i + 1; j < N; ++j) pairs.push_back({i, j});
            std::shuffle(pairs.begin(), pairs.end(), rng);
            for (auto [u, v] : pairs) {
                if ((adj[u] & adj[v]) == 0) {
                    adj[u] |= (1u << v);
                    adj[v] |= (1u << u);
                    edges++;
                }
            }

            Eval cur = eval_graph(adj, rng);
            auto score_fn = [&](const Eval &ev, int e) -> double {
                double pen_e = (e < NEED_E) ? 30.0 * (NEED_E - e) : 0.0;
                double pen_min = (ev.min_e < NEED_MIN) ? 200.0 * (NEED_MIN - ev.min_e) : 0.0;
                return pen_e + pen_min + ev.bad_cnt + 2.0 * ev.bad_deficit;
            };
            double cur_s = score_fn(cur, edges);
            double temp = 5.0;
            int stale = 0;

            for (int step = 0; step < 20000 && !found.load(); ++step) {
                if (edges >= NEED_E && cur.bad_cnt == 0) {
                    // verify triangle-free
                    bool ok = true;
                    for (int u = 0; u < N && ok; ++u)
                        for (int v = u + 1; v < N && ok; ++v)
                            if (((adj[u] >> v) & 1u) && (adj[u] & adj[v])) ok = false;
                    if (ok && !found.exchange(true)) {
                        std::lock_guard<std::mutex> lk(mtx);
                        std::cout << "=== TF WITNESS FOUND r=" << R << " n=" << N
                                  << " e=" << edges << " min_e=" << cur.min_e << " ===\n";
                        std::cout << "EDGES=[";
                        bool first = true;
                        for (int u = 0; u < N; ++u)
                            for (int v = u + 1; v < N; ++v)
                                if ((adj[u] >> v) & 1u) {
                                    if (!first) std::cout << ",";
                                    std::cout << "(" << u << "," << v << ")";
                                    first = false;
                                }
                        std::cout << "]\n" << std::flush;
                    }
                    return;
                }

                if (edges >= NEED_E && cur.bad_cnt < best_bad.load()) {
                    std::lock_guard<std::mutex> lk(mtx);
                    if (cur.bad_cnt < best_bad.load()) {
                        best_bad.store(cur.bad_cnt);
                        std::cout << "[tid=" << tid << "] NEW BEST bad=" << cur.bad_cnt
                                  << " min_e=" << cur.min_e << " deficit=" << cur.bad_deficit
                                  << " e=" << edges << "\n" << std::flush;
                    }
                }

                // Move: pick a non-edge (u,v) (prefer inside sample_bad), force-add it,
                // and remove conflicting edges (u,w) or (v,w) for each common neighbor w,
                // then greedily add any valid non-edges to stay maximal!
                int au = -1, av = -1;
                if (cur.bad_cnt > 0 && cur.sample_bad != 0 && (rng() % 100) < 75) {
                    int vs[32], vc = 0;
                    uint32_t m = cur.sample_bad;
                    while (m) { vs[vc++] = ctz(m); m &= m - 1; }
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

                // Remove triangles created by adding (au, av)
                uint32_t cn = adj[au] & adj[av];
                while (cn) {
                    int w = ctz(cn);
                    cn &= cn - 1;
                    // remove either (au, w) or (av, w)
                    if (rng() & 1) {
                        adj[au] &= ~(1u << w); adj[w] &= ~(1u << au); edges--;
                    } else {
                        adj[av] &= ~(1u << w); adj[w] &= ~(1u << av); edges--;
                    }
                }
                adj[au] |= (1u << av); adj[av] |= (1u << au); edges++;

                // Greedily saturate to maximal triangle-free (adding edges never hurts min_e or e!)
                std::vector<std::pair<int,int>> cands;
                for (int i = 0; i < N; ++i) {
                    uint32_t non = (~adj[i]) & ((1u << N) - 1u) & ~((1u << (i + 1)) - 1u);
                    while (non) {
                        int j = ctz(non);
                        non &= non - 1;
                        if ((adj[i] & adj[j]) == 0) cands.push_back({i, j});
                    }
                }
                if (!cands.empty()) {
                    std::shuffle(cands.begin(), cands.end(), rng);
                    for (auto [x, y] : cands) {
                        if ((adj[x] & adj[y]) == 0) {
                            adj[x] |= (1u << y); adj[y] |= (1u << x); edges++;
                        }
                    }
                }

                Eval nxt = eval_graph(adj, rng);
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
                if (stale > 1500) break;
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
