// Fast 20-thread adversarial tester for r=6, n=19 (alpha(G) <= 3, i.e., F = compl(G) is K_4-free)
// Checks if ANY 19-vertex graph G exists with:
//   - alpha(G) <= 3  (i.e. F is K_4-free, no 4-IS in G)
//   - max_{|S|=7} e(G[S]) <= 16  (i.e. min_{|S|=7} e(F[S]) >= 5)
//   - optional edge cap e(G) <= MAX_E (e.g. 66 from multiscale, or 62 from (5,7,7,6,6,6), or 171 unconstrained)
//   - optional multiscale check: min_{|U|=13} e(F[U]) >= 40
#include <bits/stdc++.h>
#include <thread>
#include <atomic>
using namespace std;

static constexpr int N = 19;

struct RNG {
    uint64_t s;
    RNG(uint64_t seed) : s(seed ? seed : 0x9e3779b97f4a7c15ULL) {}
    uint64_t next() {
        uint64_t x = s;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        return s = x;
    }
    int randint(int n) { return (int)(next() % (uint64_t)n); }
    double uniform() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

// Graph G stored as adjacency bitmasks
struct State {
    uint32_t adj[N];
    int edges;
    int ind4;       // number of 4-independent-sets in G (= K_4 in F)
    int dense7;     // number of 7-sets with >= 17 edges in G (<= 4 edges in F)
    int dense7_ex;  // sum of (e(S) - 16) over dense 7-sets

    void init_from_adj(const uint32_t a[N]) {
        edges = 0;
        for (int i = 0; i < N; i++) {
            adj[i] = a[i];
            edges += __builtin_popcount(a[i]);
        }
        edges /= 2;
        recompute();
    }

    // Count 4-IS in G = 4-cliques in F
    int count_ind4() const {
        uint32_t f[N];
        uint32_t full = (1u << N) - 1;
        for (int i = 0; i < N; i++) f[i] = (full ^ adj[i] ^ (1u << i));
        int cnt = 0;
        for (int a = 0; a < N; a++) {
            uint32_t m1 = f[a] & ~((1u << (a + 1)) - 1);
            while (m1) {
                int b = __builtin_ctz(m1); m1 &= m1 - 1;
                uint32_t m2 = m1 & f[b];
                while (m2) {
                    int c = __builtin_ctz(m2); m2 &= m2 - 1;
                    cnt += __builtin_popcount(m2 & f[c]);
                }
            }
        }
        return cnt;
    }

    // Enumerate all 7-sets with e(G[S]) >= 17 (i.e. e(F[S]) <= 4)
    // Since N=19, C(19,7) = 50,388 - TINY! We can even precompute or do fast recursive branch-and-bound!
    void count_dense7(int &cnt, int &ex) const {
        cnt = 0; ex = 0;
        // Branch and bound on F: choose 7 vertices with total F-edges <= 4
        uint32_t f[N];
        uint32_t full = (1u << N) - 1;
        for (int i = 0; i < N; i++) f[i] = (full ^ adj[i] ^ (1u << i));

        int cur[7];
        auto dfs = [&](auto &self, int start, int depth, int fedges) -> void {
            if (depth == 7) {
                cnt++;
                ex += (5 - fedges);
                return;
            }
            int need = 7 - depth;
            for (int v = start; v <= N - need; v++) {
                int add = 0;
                uint32_t fv = f[v];
                for (int i = 0; i < depth; i++) add += (fv >> cur[i]) & 1;
                if (fedges + add <= 4) {
                    cur[depth] = v;
                    self(self, v + 1, depth + 1, fedges + add);
                }
            }
        };
        dfs(dfs, 0, 0, 0);
    }

    void recompute() {
        ind4 = count_ind4();
        count_dense7(dense7, dense7_ex);
    }

    // Incremental delta for flipping edge (u, v) in G
    // Wait: N=19, delta_ind4 is O(N) (count common F-neighbors of u, v that are F-adjacent!)
    int delta_ind4_if_flip(int u, int v) const {
        // If (u,v) is currently an edge in G, removing it adds (u,v) to F, creating K4s containing {u,v}.
        // Common F-neighbors of u and v:
        uint32_t full = (1u << N) - 1;
        uint32_t fu = full ^ adj[u] ^ (1u << u);
        uint32_t fv = full ^ adj[v] ^ (1u << v);
        uint32_t cm = fu & fv & ~(1u << u) & ~(1u << v);
        int k4 = 0;
        uint32_t m = cm;
        while (m) {
            int a = __builtin_ctz(m); m &= m - 1;
            uint32_t fa = full ^ adj[a] ^ (1u << a);
            k4 += __builtin_popcount(m & fa);
        }
        bool has_edge = (adj[u] >> v) & 1;
        return has_edge ? +k4 : -k4;
    }

    // Incremental delta for dense7 on flipping (u,v): enumerate 5-subsets of V\{u,v} with fedges_on_7 <= 5
    void delta_dense7_if_flip(int u, int v, int &dcnt, int &dex) const {
        dcnt = 0; dex = 0;
        bool has_edge = (adj[u] >> v) & 1;
        // Before flip: if has_edge, F does NOT have (u,v); after flip, F DOES have (u,v) (+1 f-edge).
        // If !has_edge, F HAS (u,v); after flip, F does NOT have (u,v) (-1 f-edge).
        // We need all 5-subsets T of V\{u,v} such that f_edges(T u {u,v}) without (u,v) is <= 4!
        uint32_t full = (1u << N) - 1;
        uint32_t f[N];
        for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u << i);
        // Remove (u,v) from f temporarily for uniform counting
        f[u] &= ~(1u << v);
        f[v] &= ~(1u << u);

        int verts[N]; int nv = 0;
        for (int i = 0; i < N; i++) if (i != u && i != v) verts[nv++] = i;
        int fuv_deg[N];
        for (int i = 0; i < nv; i++) {
            int w = verts[i];
            fuv_deg[i] = ((f[u] >> w) & 1) + ((f[v] >> w) & 1);
        }

        int cur[5];
        auto dfs = [&](auto &self, int idx, int depth, int fe) -> void {
            if (depth == 5) {
                // fe = F-edges in T u {u,v} EXCLUDING (u,v).
                // If has_edge: before = fe, after = fe + 1.
                //   before <= 4 -> was dense (ex 5-fe); after <= 4 iff fe <= 3 (ex 4-fe).
                // If !has_edge: before = fe + 1, after = fe.
                if (has_edge) {
                    if (fe == 4) { dcnt -= 1; dex -= 1; }
                    else { dex -= 1; } // fe <= 3: still dense, ex drops by 1
                } else {
                    if (fe == 4) { dcnt += 1; dex += 1; }
                    else { dex += 1; }
                }
                return;
            }
            int need = 5 - depth;
            for (int i = idx; i <= nv - need; i++) {
                int w = verts[i];
                int add = fuv_deg[i];
                uint32_t fw = f[w];
                for (int j = 0; j < depth; j++) add += (fw >> cur[j]) & 1;
                if (fe + add <= 4) {
                    cur[depth] = w;
                    self(self, i + 1, depth + 1, fe + add);
                }
            }
        };
        dfs(dfs, 0, 0, 0);
    }

    void flip(int u, int v) {
        int di = delta_ind4_if_flip(u, v);
        int dc, dx;
        delta_dense7_if_flip(u, v, dc, dx);
        bool has_edge = (adj[u] >> v) & 1;
        adj[u] ^= (1u << v);
        adj[v] ^= (1u << u);
        edges += has_edge ? -1 : +1;
        ind4 += di;
        dense7 += dc;
        dense7_ex += dx;
    }
};

// Check multiscale_2r_plus_1: min_{|U|=13} e(F[U]) >= 40
int check_min13(const uint32_t adj[N]) {
    uint32_t full = (1u << N) - 1;
    uint32_t f[N];
    for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u << i);
    // Complement of U (size 6): C(19,6) = 27,132! Exact check in 0.2ms!
    int total_f = 0;
    int fdeg[N];
    for (int i = 0; i < N; i++) { fdeg[i] = __builtin_popcount(f[i]); total_f += fdeg[i]; }
    total_f /= 2;
    int min13 = 999999;
    // Choose 6 vertices to exclude: e(F[V\W]) = total_f - sum_{w in W} fdeg[w] + e(F[W])
    for (int a = 0; a < N; a++)
      for (int b = a+1; b < N; b++) {
        int eab = (f[a] >> b) & 1;
        for (int c = b+1; c < N; c++) {
          int eabc = eab + ((f[a]>>c)&1) + ((f[b]>>c)&1);
          for (int d = c+1; d < N; d++) {
            int eabcd = eabc + ((f[a]>>d)&1) + ((f[b]>>d)&1) + ((f[c]>>d)&1);
            for (int e = d+1; e < N; e++) {
              int eabcde = eabcd + ((f[a]>>e)&1) + ((f[b]>>e)&1) + ((f[c]>>e)&1) + ((f[d]>>e)&1);
              for (int g = e+1; g < N; g++) {
                int ew = eabcde + ((f[a]>>g)&1) + ((f[b]>>g)&1) + ((f[c]>>g)&1) + ((f[d]>>g)&1) + ((f[e]>>g)&1);
                int e13 = total_f - (fdeg[a]+fdeg[b]+fdeg[c]+fdeg[d]+fdeg[e]+fdeg[g]) + ew;
                if (e13 < min13) min13 = e13;
              }
            }
          }
        }
      }
    return min13;
}

int main(int argc, char** argv) {
    int max_e = (argc > 1) ? atoi(argv[1]) : 171;
    int iters = (argc > 2) ? atoi(argv[2]) : 2000000;
    int nthreads = 20;

    // Self-test incremental deltas on 50 random flips
    {
        RNG rng(12345);
        uint32_t a[N] = {};
        for (int i = 0; i < N; i++)
            for (int j = i+1; j < N; j++)
                if (rng.randint(100) < 40) { a[i] |= (1u<<j); a[j] |= (1u<<i); }
        State st; st.init_from_adj(a);
        for (int t = 0; t < 50; t++) {
            int u = rng.randint(N), v = rng.randint(N);
            if (u == v) continue;
            st.flip(u, v);
            State ref; ref.init_from_adj(st.adj);
            if (st.ind4 != ref.ind4 || st.dense7 != ref.dense7 || st.dense7_ex != ref.dense7_ex || st.edges != ref.edges) {
                cerr << "SELF-TEST FAILED!\n";
                return 1;
            }
        }
        cout << "Self-test passed (50 flips exact). Searching N=19, max_e=" << max_e << ", iters=" << iters << " x " << nthreads << " threads...\n";
    }

    atomic<bool> found(false);
    atomic<int> best_total(999999);
    mutex mtx;

    auto worker = [&](int tid) {
        RNG rng(0x123456789abcdefULL ^ ((uint64_t)tid * 0x9e3779b97f4a7c15ULL));
        uint32_t a[N] = {};
        // Start with random graph with ~min(max_e, 60) edges
        int target = min(max_e, 60);
        vector<pair<int,int>> pairs;
        for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++) pairs.push_back({i,j});
        for (int i = (int)pairs.size()-1; i > 0; i--) swap(pairs[i], pairs[rng.randint(i+1)]);
        for (int i = 0; i < target; i++) {
            a[pairs[i].first] |= (1u << pairs[i].second);
            a[pairs[i].second] |= (1u << pairs[i].first);
        }
        State st; st.init_from_adj(a);
        double T0 = 2.0, T1 = 0.02;
        int w_ind = (tid % 2 == 0) ? 1 : 2;
        int w_den = (tid % 2 == 0) ? 2 : 1;

        for (int step = 0; step < iters && !found.load(memory_order_relaxed); step++) {
            int cur_pen = st.ind4 + st.dense7_ex;
            if (cur_pen == 0 && st.edges <= max_e) {
                int m13 = check_min13(st.adj);
                lock_guard<mutex> lk(mtx);
                if (!found.exchange(true)) {
                    cout << "!!! WITNESS FOUND (tid=" << tid << ", step=" << step << ") !!!\n";
                    cout << "edges(G)=" << st.edges << " edges(F)=" << (171 - st.edges)
                         << " ind4=" << st.ind4 << " dense7=" << st.dense7
                         << " min_{|U|=13} e(F[U])=" << m13 << "\n";
                    cout << "G degrees:";
                    for (int i = 0; i < N; i++) cout << " " << __builtin_popcount(st.adj[i]);
                    cout << "\n";
                }
                return;
            }
            if (cur_pen < best_total.load(memory_order_relaxed)) {
                int old = best_total.load();
                while (cur_pen < old && !best_total.compare_exchange_weak(old, cur_pen)) {}
                if (cur_pen == best_total.load()) {
                    lock_guard<mutex> lk(mtx);
                    cout << "[tid=" << tid << " step=" << step << "] best ind4+dex=" << cur_pen
                         << " (ind4=" << st.ind4 << ", dense7=" << st.dense7 << ", dex=" << st.dense7_ex
                         << ", e=" << st.edges << ")\n";
                }
            }

            double frac = (double)step / (double)iters;
            double T = T0 * pow(T1 / T0, frac);

            int u = rng.randint(N), v = rng.randint(N - 1);
            if (v >= u) v++;
            bool has_e = (st.adj[u] >> v) & 1;
            if (!has_e && st.edges >= max_e) continue;

            int di = st.delta_ind4_if_flip(u, v);
            int dc, dx;
            st.delta_dense7_if_flip(u, v, dc, dx);
            int dE = w_ind * di + w_den * dx;
            if (dE <= 0 || rng.uniform() < exp(-(double)dE / T)) {
                st.adj[u] ^= (1u << v);
                st.adj[v] ^= (1u << u);
                st.edges += has_e ? -1 : +1;
                st.ind4 += di;
                st.dense7 += dc;
                st.dense7_ex += dx;
            }
        }
    };

    vector<thread> ts;
    for (int i = 0; i < nthreads; i++) ts.emplace_back(worker, i);
    for (auto &t : ts) t.join();
    if (!found) cout << "NO WITNESS FOUND. Best ind4+dex = " << best_total.load() << "\n";
    return 0;
}
