// Adversarial check:
// Mode 0: N=13, alpha <= 2, max_{|S|=7} e(G[S]) <= 16 (unconstrained edges!)
// Mode 1: N=19, alpha <= 3, max_{|S|=7} e(G[S]) <= 16, WITH deg(0) <= 6 (unconstrained edges!)
// Mode 2: N=19, alpha <= 3, max_{|S|=7} e(G[S]) <= 16, WITH deg(0) <= 6 AND e(G) <= 66
#include <bits/stdc++.h>
#include <thread>
#include <atomic>
using namespace std;

struct RNG {
    uint64_t s;
    RNG(uint64_t seed) : s(seed ? seed : 0x9e3779b97f4a7c15ULL) {}
    uint64_t next() { uint64_t x = s; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return s = x; }
    int randint(int n) { return (int)(next() % (uint64_t)n); }
    double uniform() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

// Mode 0: N=13, alpha <= 2 (no 3-IS = F is triangle-free), max_{|S|=7} e(G[S]) <= 16 (min_7 F >= 5)
void run_n13() {
    constexpr int N = 13;
    atomic<bool> found(false);
    atomic<int> best(999999);
    mutex mtx;
    auto worker = [&](int tid) {
        RNG rng(1000 + tid * 1337ULL);
        uint32_t adj[N] = {};
        for (int i = 0; i < N; i++)
            for (int j = i+1; j < N; j++)
                if (rng.randint(100) < 55) { adj[i] |= 1u<<j; adj[j] |= 1u<<i; }
        auto eval = [&](int &ind3, int &dex) {
            uint32_t full = (1u<<N)-1, f[N];
            for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u<<i);
            ind3 = 0;
            for (int a = 0; a < N; a++) {
                uint32_t m = f[a] & ~((1u<<(a+1))-1);
                while (m) { int b = __builtin_ctz(m); m &= m-1; ind3 += __builtin_popcount(m & f[b]); }
            }
            dex = 0;
            int cur[7];
            auto dfs = [&](auto &self, int st, int dep, int fe) -> void {
                if (dep == 7) { dex += (5 - fe); return; }
                for (int v = st; v <= N - (7 - dep); v++) {
                    int add = 0; uint32_t fv = f[v];
                    for (int i = 0; i < dep; i++) add += (fv >> cur[i]) & 1;
                    if (fe + add <= 4) { cur[dep] = v; self(self, v+1, dep+1, fe+add); }
                }
            };
            dfs(dfs, 0, 0, 0);
        };
        int ind3, dex; eval(ind3, dex);
        for (int step = 0; step < 200000 && !found; step++) {
            int pen = ind3 + dex;
            if (pen == 0) {
                lock_guard<mutex> lk(mtx);
                if (!found.exchange(true)) {
                    int e = 0; for (int i = 0; i < N; i++) e += __builtin_popcount(adj[i]);
                    cout << "[N=13] WITNESS FOUND! e(G)=" << e/2 << " e(F)=" << (78 - e/2) << "\n";
                }
                return;
            }
            if (pen < best) { int old = best; while (pen < old && !best.compare_exchange_weak(old, pen)) {} }
            int u = rng.randint(N), v = rng.randint(N-1); if (v >= u) v++;
            adj[u] ^= 1u<<v; adj[v] ^= 1u<<u;
            int ni, nd; eval(ni, nd);
            double T = 1.5 * pow(0.01, (double)step / 200000.0);
            int dE = (ni + nd) - (ind3 + dex);
            if (dE <= 0 || rng.uniform() < exp(-(double)dE / T)) { ind3 = ni; dex = nd; }
            else { adj[u] ^= 1u<<v; adj[v] ^= 1u<<u; }
        }
    };
    vector<thread> ts; for (int i = 0; i < 20; i++) ts.emplace_back(worker, i);
    for (auto &t : ts) t.join();
    if (!found) cout << "[N=13] NO WITNESS FOUND. Best ind3+dex = " << best.load() << "\n";
}

// Mode 1/2: N=19 with deg(0) = 6 (neighbors of 0 fixed to {1..6}, non-neighbors {7..18})
void run_n19_deg6(int max_e, int iters) {
    constexpr int N = 19;
    atomic<bool> found(false);
    atomic<int> best(999999);
    mutex mtx;
    auto worker = [&](int tid) {
        RNG rng(2000 + tid * 9973ULL);
        uint32_t adj[N] = {};
        // Vertex 0 adjacent ONLY to {1,2,3,4,5,6}
        for (int j = 1; j <= 6; j++) { adj[0] |= 1u<<j; adj[j] |= 1u<<0; }
        // Random edges among {1..18}
        int e = 6;
        for (int i = 1; i < N; i++)
            for (int j = i+1; j < N; j++)
                if (e < max_e && rng.randint(100) < 42) { adj[i] |= 1u<<j; adj[j] |= 1u<<i; e++; }
        auto eval_ind4 = [&]() {
            uint32_t full = (1u<<N)-1, f[N];
            for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u<<i);
            int cnt = 0;
            for (int a = 0; a < N; a++) {
                uint32_t m1 = f[a] & ~((1u<<(a+1))-1);
                while (m1) {
                    int b = __builtin_ctz(m1); m1 &= m1-1;
                    uint32_t m2 = m1 & f[b];
                    while (m2) { int c = __builtin_ctz(m2); m2 &= m2-1; cnt += __builtin_popcount(m2 & f[c]); }
                }
            }
            return cnt;
        };
        auto eval_dex = [&]() {
            uint32_t full = (1u<<N)-1, f[N];
            for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u<<i);
            int dex = 0, cur[7];
            auto dfs = [&](auto &self, int st, int dep, int fe) -> void {
                if (dep == 7) { dex += (5 - fe); return; }
                for (int v = st; v <= N - (7 - dep); v++) {
                    int add = 0; uint32_t fv = f[v];
                    for (int i = 0; i < dep; i++) add += (fv >> cur[i]) & 1;
                    if (fe + add <= 4) { cur[dep] = v; self(self, v+1, dep+1, fe+add); }
                }
            };
            dfs(dfs, 0, 0, 0);
            return dex;
        };
        auto delta_ind4 = [&](int u, int v) {
            uint32_t full = (1u<<N)-1;
            uint32_t fu = full ^ adj[u] ^ (1u<<u), fv = full ^ adj[v] ^ (1u<<v);
            uint32_t cm = fu & fv & ~(1u<<u) & ~(1u<<v);
            int k4 = 0; uint32_t m = cm;
            while (m) { int a = __builtin_ctz(m); m &= m-1; k4 += __builtin_popcount(m & (full ^ adj[a] ^ (1u<<a))); }
            return ((adj[u]>>v)&1) ? +k4 : -k4;
        };
        auto delta_dex = [&](int u, int v) {
            bool has_e = (adj[u]>>v)&1;
            uint32_t full = (1u<<N)-1, f[N];
            for (int i = 0; i < N; i++) f[i] = full ^ adj[i] ^ (1u<<i);
            f[u] &= ~(1u<<v); f[v] &= ~(1u<<u);
            int verts[N], nv = 0, fd[N];
            for (int i = 0; i < N; i++) if (i != u && i != v) {
                verts[nv] = i; fd[nv] = ((f[u]>>i)&1) + ((f[v]>>i)&1); nv++;
            }
            int dx = 0, cur[5];
            auto dfs = [&](auto &self, int idx, int dep, int fe) -> void {
                if (dep == 5) { dx += has_e ? -1 : +1; return; }
                for (int i = idx; i <= nv - (5 - dep); i++) {
                    int w = verts[i], add = fd[i]; uint32_t fw = f[w];
                    for (int j = 0; j < dep; j++) add += (fw >> cur[j]) & 1;
                    if (fe + add <= 4) { cur[dep] = w; self(self, i+1, dep+1, fe+add); }
                }
            };
            dfs(dfs, 0, 0, 0);
            return dx;
        };
        int ind4 = eval_ind4(), dex = eval_dex();
        for (int step = 0; step < iters && !found; step++) {
            int pen = ind4 + dex;
            if (pen == 0) {
                lock_guard<mutex> lk(mtx);
                if (!found.exchange(true)) {
                    cout << "[N=19 deg(0)=6 max_e=" << max_e << "] WITNESS FOUND! e(G)=" << e << "\n";
                    cout << "  degrees:";
                    for (int i = 0; i < N; i++) cout << " " << __builtin_popcount(adj[i]);
                    cout << "\n  B_2 missing edges (on 1..6): ";
                    int m2 = 0;
                    for (int i = 1; i <= 6; i++) for (int j = i+1; j <= 6; j++) if (!((adj[i]>>j)&1)) m2++;
                    int cr = 0;
                    for (int i = 1; i <= 6; i++) for (int j = 7; j < N; j++) if ((adj[i]>>j)&1) cr++;
                    int eA = 0;
                    for (int i = 7; i < N; i++) for (int j = i+1; j < N; j++) if ((adj[i]>>j)&1) eA++;
                    cout << m2 << ", cross(A2,B2)=" << cr << ", e(A2)=" << eA << "\n";
                }
                return;
            }
            if (pen < best) { int old = best; while (pen < old && !best.compare_exchange_weak(old, pen)) {} }
            // Only flip edges among {1..18} so deg(0)=6 stays exact!
            int u = 1 + rng.randint(N - 1), v = 1 + rng.randint(N - 2);
            if (v >= u) v++;
            bool has_e = (adj[u]>>v)&1;
            if (!has_e && e >= max_e) continue;
            int di = delta_ind4(u, v), dx = delta_dex(u, v);
            double T = 1.5 * pow(0.015, (double)step / (double)iters);
            int dE = di + 2 * dx;
            if (dE <= 0 || rng.uniform() < exp(-(double)dE / T)) {
                adj[u] ^= 1u<<v; adj[v] ^= 1u<<u;
                e += has_e ? -1 : +1;
                ind4 += di; dex += dx;
            }
        }
    };
    vector<thread> ts; for (int i = 0; i < 20; i++) ts.emplace_back(worker, i);
    for (auto &t : ts) t.join();
    if (!found) cout << "[N=19 deg(0)=6 max_e=" << max_e << "] NO WITNESS FOUND. Best ind4+dex = " << best.load() << "\n";
}

int main() {
    run_n13();
    run_n19_deg6(171, 400000);
    run_n19_deg6(66, 400000);
    return 0;
}
