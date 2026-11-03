// Seed program (island "path"): bgpa (prefix-anchored DFS annealing) from beckett-gray-9/src/bgpa.cpp,
// pa mode only, adapted to the evolve I/O contract.
//
// Inner solver: randomized pruned DFS over queue moves (pop the queue head, or push an absent bit), restricted
// to unvisited words.  Pruning: Sawada-Wong pendant rule with forced moves, a level (Euler) count, first-on
// symmetry breaking (a never-used bit may only be pushed if it is the smallest never-used bit).
// Outer loop: anchor P = a partial code.  Move: cut P back by K in [kmin,kmax] (or to 0 with probability p0),
// DFS from the cut with a node budget, take the deepest path Q found; accept Q with Metropolis on depth (pa_T).
//
// Contract: prog --n N --seed S --time T   (T = CPU seconds; the evaluator kills the process soon after T)
//   prints "BEST <missing words>" then "CERT <n> <transition digits>" (the deepest valid partial code found,
//   from word 0) about once per CPU second and at exit, and "CODE <n> <digits>" if a code is found.
// Defaults are the n=8 lane p8 settings (paT 0.5, budget 3e6, K 40-160, p0 0.02), which found an 8-bit code.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <ctime>
#include <cmath>
#include <string>
#include <vector>
#include <random>
#include <algorithm>

static int n, N;
static std::vector<uint8_t> visited;
static std::vector<int16_t> deg;      // # unvisited neighbours
static int q[64], qh = 0, qlen = 0;   // queue ring buffer (size 64 > n)
static int path[1 << 16];             // transitions
static int depth = 0;                 // number of transitions made; words visited = depth+1
static uint32_t usedmask = 0;         // bits ever pushed
static bool symbreak = true;
static uint64_t nodes = 0, budget = 0;
static int best = 0;
static std::vector<int> bestpath;
static std::mt19937_64 rng;
static bool stop_flag = false;
static std::vector<int> solution;
static std::vector<float> wtab;       // learned branching priorities w[word*n+bit]
static int gbest_cur = -1;            // mirrors gbest

static inline int pc(int x) { return __builtin_popcount(x); }
static double cpu_now() { timespec ts; clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static inline int avail(int u, int cur) {
    int a = deg[u];
    if (pc(u ^ cur) == 1) a++;
    if (pc(u) == 1) a++;
    return a;
}

static int rlev[33];                 // unvisited count per level

static void visit(int v) {
    visited[v] = 1; rlev[pc(v)]--;
    for (int b = 0; b < n; b++) deg[v ^ (1 << b)]--;
}
static void unvisit(int v) {
    visited[v] = 0; rlev[pc(v)]++;
    for (int b = 0; b < n; b++) deg[v ^ (1 << b)]++;
}

// Level (Euler) count: the rest of the cycle is a walk cur -> ... -> 0 on levels; with c_k path
// edges between levels k and k+1:  c_{k-1} + c_k = 2 r_k + [k==l] + [k==0].
static bool level_ok(int l) {
    int c = 0;  // c_{k-1}
    int above = 0; for (int k = 0; k <= n; k++) above += rlev[k];
    for (int k = 0; k <= n; k++) {
        int ck = 2 * rlev[k] + (k == l) + (k == 0) - c;
        if (ck < 0) return false;
        above -= rlev[k];
        if (k == n) { if (ck != 0) return false; }
        else if (ck == 0 && (above > 0 || l > k)) return false;
        c = ck;
    }
    return true;
}

// returns false if the position (just arrived at cur from prev) is dead
static bool feasible(int cur, int prev, int &forced) {
    forced = -1;
    if (!level_ok(pc(cur))) return false;
    if (prev >= 0)
        for (int b = 0; b < n; b++) {
            int u = prev ^ (1 << b);
            if (!visited[u] && avail(u, cur) < 2) return false;
        }
    for (int b = 0; b < n; b++) {
        int u = cur ^ (1 << b);
        if (visited[u]) continue;
        int a = avail(u, cur);
        if (a < 2) return false;
        if (a == 2 && pc(u) != 1) {   // must be entered from cur and left by its other neighbour
            if (forced >= 0) return false;
            forced = u;
        }
    }
    {
        int R = N - depth - 1;
        if (R > 0 && R <= std::max(16, N / 16)) {
            int un[1 << 12], m = 0, dead = 0;
            for (int w = 0; w < N; w++) {
                if (visited[w]) continue;
                un[m++] = w;
                if (pc(w) != 1 && avail(w, cur) < 2) { if (++dead > 1) return false; }
            }
            int start = -1;
            for (int b = 0; b < n; b++) { int u = cur ^ (1 << b); if (!visited[u]) { start = u; break; } }
            if (start < 0) return false;
            static std::vector<uint8_t> cseen;
            if ((int)cseen.size() != N) cseen.assign(N, 0);
            else for (int i = 0; i < m; i++) cseen[un[i]] = 0;
            int stk[1 << 12], sp = 0, reached = 0;
            bool nb0 = false;
            stk[sp++] = start; cseen[start] = 1;
            while (sp) {
                int x = stk[--sp];
                reached++;
                if (pc(x) == 1) nb0 = true;
                for (int b = 0; b < n; b++) {
                    int w = x ^ (1 << b);
                    if (!visited[w] && !cseen[w]) { cseen[w] = 1; stk[sp++] = w; }
                }
            }
            for (int i = 0; i < m; i++) cseen[un[i]] = 0;
            if (reached != m || !nb0) return false;
        }
    }
    return true;
}

static int bestcnt = 1 << 30;
static std::vector<uint8_t> rseen;
static int rstk[1 << 12];
static int resid_count() {
    if ((int)rseen.size() != N) rseen.assign(N, 0);
    else std::fill(rseen.begin(), rseen.end(), 0);
    int comps = 0, iso = 0;
    for (int s = 0; s < N; s++) {
        if (visited[s] || rseen[s]) continue;
        comps++;
        if (deg[s] == 0) iso++;
        int sp = 0; rstk[sp++] = s; rseen[s] = 1;
        while (sp) {
            int u = rstk[--sp];
            for (int b = 0; b < n; b++) {
                int w = u ^ (1 << b);
                if (!visited[w] && !rseen[w]) { rseen[w] = 1; rstk[sp++] = w; }
            }
        }
    }
    return comps + iso;
}

static void dfs(int cur, uint64_t alloc) {
    if (stop_flag) return;
    nodes++;
    if (budget && nodes > budget) { stop_flag = true; return; }
    const uint64_t endn = nodes + alloc;
    if (depth + 1 == N) {  // all words visited; must close to 0
        if (pc(cur) == 1) {
            path[depth] = __builtin_ctz(cur);   // queue holds just this bit, so popping it is legal
            solution.assign(path, path + N); stop_flag = true;
        }
        return;
    }
    int cand[64], nc = 0;
    if (qlen > 0) {   // pop
        int h = q[qh];
        int v = cur ^ (1 << h);
        if (!visited[v] && v != 0) cand[nc++] = h;
    }
    int firstunused = usedmask == 0 ? 0 : 32 - __builtin_clz(usedmask);  // used bits are 0..k-1
    for (int b = 0; b < n; b++) {   // push
        if (cur >> b & 1) continue;
        if (symbreak && !(usedmask >> b & 1) && b != firstunused) continue;
        int v = cur | (1 << b);
        if (!visited[v]) cand[nc++] = b;
    }
    if (nc == 0) return;
    // ordering: random shuffle, then stable sort by # unvisited neighbours of the target (Warnsdorff)
    int key[64]; double sec[64];
    for (int i = 0; i < nc; i++) {
        key[i] = deg[cur ^ (1 << cand[i])];
        double u = ((rng() >> 11) + 0.5) * (1.0 / 9007199254740992.0);
        sec[i] = wtab[(size_t)cur * n + cand[i]] - std::log(-std::log(u));
    }
    for (int i = 1; i < nc; i++) { int c = cand[i], k = key[i], j = i - 1; double s = sec[i];
        while (j >= 0 && (key[j] > k || (key[j] == k && sec[j] < s))) {
            cand[j + 1] = cand[j]; key[j + 1] = key[j]; sec[j + 1] = sec[j]; j--; }
        cand[j + 1] = c; key[j + 1] = k; sec[j + 1] = s; }
    for (int i = 0; i < nc && !stop_flag; i++) {
        if (nodes >= endn) break;
        uint64_t rem = endn - nodes;
        uint64_t ca;
        if (i == nc - 1) ca = rem;
        else if (depth >= gbest_cur - std::max(8, N / 32)) ca = std::max<uint64_t>(1, rem / (uint64_t)(nc - i));
        else ca = std::max<uint64_t>(1, rem / 2);
        int b = cand[i];
        int v = cur ^ (1 << b);
        bool ispop = (cur >> b) & 1;
        int saved_used = usedmask;
        if (ispop) { qh = (qh + 1) & 63; qlen--; }
        else { q[(qh + qlen) & 63] = b; qlen++; usedmask |= 1u << b; }
        visit(v);
        path[depth++] = b;
        int forced;
        if (feasible(v, cur, forced)) {
            if (depth >= best) {
                int cnt = resid_count();
                if (depth > best || cnt < bestcnt) { best = depth; bestcnt = cnt; bestpath.assign(path, path + depth); }
            }
            if (forced >= 0) {
                // the only continuation must go to `forced`; check it is a legal move
                int fb = __builtin_ctz(forced ^ v);
                bool ok;
                if (v >> fb & 1) ok = (qlen > 0 && q[qh] == fb);
                else ok = !symbreak || (usedmask >> fb & 1) || fb == (usedmask == 0 ? 0 : 32 - __builtin_clz(usedmask));
                if (ok) dfs(v, rem);
            } else dfs(v, ca);
        }
        depth--;
        unvisit(v);
        if (ispop) { qh = (qh - 1) & 63; q[qh] = b; qlen++; }
        else { qlen--; usedmask = saved_used; }
    }
}

static std::string prefix;
static int reset_and_prefix() {
    std::fill(visited.begin(), visited.end(), 0); std::fill(deg.begin(), deg.end(), n);
    for (int k = 0; k <= n; k++) { long c = 1; for (int j = 0; j < k; j++) c = c * (n - j) / (j + 1); rlev[k] = (int)c; }
    qh = 0; qlen = 0; depth = 0; usedmask = 0;
    visit(0);
    int cur = 0;
    for (char c : prefix) {
        int b = c - '0';
        int v = cur ^ (1 << b);
        if (cur >> b & 1) { qh = (qh + 1) & 63; qlen--; }
        else { q[(qh + qlen) & 63] = b; qlen++; usedmask |= 1u << b; }
        visit(v); path[depth++] = b; cur = v;
    }
    return cur;
}

static std::string gbestcert;
static int gbest = -1;
static void report() {
    printf("BEST %d\nCERT %d %s\n", N - (gbest + 1), n, gbestcert.c_str());
    fflush(stdout);
}

int main(int argc, char **argv) {
    uint64_t seed = 1;
    double tlimit = 60;
    int pa_kmin = 40, pa_kmax = 160;
    uint64_t pa_budget = 700000;
    double pa_T = 0.5, pa_p0 = 0.02;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--n") n = atoi(argv[++i]);
        else if (a == "--seed") seed = strtoull(argv[++i], 0, 10);
        else if (a == "--time") tlimit = atof(argv[++i]);
        else { fprintf(stderr, "unknown arg %s\n", a.c_str()); return 2; }
    }
    N = 1 << n;
    rng.seed(seed);
    visited.assign(N, 0); deg.assign(N, n);
    wtab.assign((size_t)N * n, 0.0f);
    double t0 = cpu_now(), last = t0;
    std::string P;
    double Pcnt = 0.0, gbcnt = 1e9;
    const int POOL = 4;
    std::string pool[POOL];
    double poolcnt[POOL] = {0.0, 0.0, 0.0, 0.0};
    uint64_t moves = 0;
    while (cpu_now() - t0 < tlimit) {
        int slot = 0;
        bool acc = false;
        {
            int mx = 0;
            for (int j = 0; j < POOL; j++) mx = std::max(mx, (int)pool[j].size());
            double w[POOL], tot = 0;
            for (int j = 0; j < POOL; j++) { w[j] = std::exp(((double)pool[j].size() - mx) / 2.0); tot += w[j]; }
            double r = (rng() >> 11) * (1.0 / 9007199254740992.0) * tot;
            slot = POOL - 1;
            for (int j = 0; j < POOL; j++) { if (r < w[j]) { slot = j; break; } r -= w[j]; }
            P = pool[slot]; Pcnt = poolcnt[slot];
        }
        int d = (int)P.size();
        double uk = (rng() >> 11) * (1.0 / 9007199254740992.0);
        int K = (int)std::exp(std::log(10.0) + uk * (std::log(300.0) - std::log(10.0)));
        if (K < 1) K = 1;
        int cut = std::max(0, d - K);
        if (pa_p0 > 0 && (rng() >> 11) * (1.0 / 9007199254740992.0) < pa_p0) cut = 0;
        prefix = P.substr(0, cut);
        {
            int bbest = -1;
            int bbcnt = 1 << 30;
            std::vector<int> bbp;
            for (int r = 0; r < 7; r++) {
                if (r > 0) {
                    int hi = std::max(10, K / 2);
                    double uk2 = (rng() >> 11) * (1.0 / 9007199254740992.0);
                    int Kr = (int)std::exp(std::log(10.0) + uk2 * (std::log((double)hi) - std::log(10.0)));
                    if (Kr < 1) Kr = 1;
                    int c2 = std::max(0, (int)bbp.size() - Kr);
                    prefix.clear();
                    for (int i = 0; i < c2; i++) prefix += char('0' + bbp[i]);
                }
                int cur0 = reset_and_prefix();
                best = depth; bestcnt = 1 << 30; bestpath.assign(path, path + depth);
                nodes = 0; budget = pa_budget / 7; stop_flag = false;
                dfs(cur0, budget ? budget : (uint64_t)1 << 60);
                if (best > bbest || (best == bbest && bestcnt < bbcnt)) { bbest = best; bbcnt = bestcnt; bbp = bestpath; }
                if (!solution.empty()) break;
            }
            best = bbest; bestpath = bbp; bestcnt = bbcnt;
        }
        moves++;
        if (!solution.empty()) {
            gbest = N - 1; gbestcert.clear(); for (int b : solution) gbestcert += char('0' + b);
            report();
            printf("CODE %d %s\n", n, gbestcert.c_str());
            fflush(stdout);
            return 0;
        }
        int nd = best;
        {
            float delta = nd > d ? 0.5f : (nd == d ? 0.1f : -0.1f);
            int wc = 0;
            for (int i = 0; i < nd && i < (int)bestpath.size(); i++) {
                int b = bestpath[i];
                if (i >= cut) {
                    float &x = wtab[(size_t)wc * n + b];
                    x += delta;
                    if (x > 3.0f) x = 3.0f;
                    if (x < -3.0f) x = -3.0f;
                }
                wc ^= 1 << b;
            }
        }
        double u = (rng() >> 11) * (1.0 / 9007199254740992.0);
        double ncnt = bestcnt >= (1 << 29) ? 0.0 : (double)bestcnt;
        double dE = (nd - 0.5 * ncnt) - (d - 0.5 * Pcnt);
        if (dE >= 0 || (pa_T > 0 && u < std::exp(dE / pa_T))) {
            P.clear(); for (int b : bestpath) P += char('0' + b);
            Pcnt = ncnt;
            pool[slot] = P; poolcnt[slot] = Pcnt;
            acc = true;
        }
        if (!acc) {
            int sh = 0;
            for (int j = 1; j < POOL; j++)
                if (pool[j].size() < pool[sh].size() || (pool[j].size() == pool[sh].size() && poolcnt[j] > poolcnt[sh])) sh = j;
            int L = (int)bestpath.size();
            if (L >= (int)pool[sh].size() && (L > (int)pool[sh].size() || ncnt <= poolcnt[sh])) {
                bool ok = true;
                for (int j = 0; j < POOL && ok; j++) {
                    if (j == sh) continue;
                    int l = 0, m = std::min(L, (int)pool[j].size());
                    while (l < m && pool[j][l] - '0' == bestpath[l]) l++;
                    if (L - l <= 64) ok = false;
                }
                if (ok) {
                    pool[sh].clear(); for (int b : bestpath) pool[sh] += char('0' + b);
                    poolcnt[sh] = ncnt;
                }
            }
        }
        if (nd > gbest || (nd == gbest && ncnt < gbcnt)) {
            gbest = nd; gbest_cur = nd; gbcnt = ncnt; gbestcert.clear(); for (int b : bestpath) gbestcert += char('0' + b);
            bool again = true;
            while (again && solution.empty() && cpu_now() - t0 < tlimit) {
                again = false;
                if (N - (gbest + 1) > std::max(16, N / 16)) break;
                static const int Ls[4] = {16, 32, 64, 128};
                std::string base = gbestcert;
                for (int li = 0; li < 4 && !again; li++) {
                    if (cpu_now() - t0 >= tlimit) break;
                    int c2 = gbest - Ls[li];
                    if (c2 < 0) continue;
                    prefix = base.substr(0, c2);
                    int cur0 = reset_and_prefix();
                    best = depth; bestcnt = 1 << 30; bestpath.assign(path, path + depth);
                    nodes = 0; budget = 4 * pa_budget; stop_flag = false;
                    dfs(cur0, budget);
                    if (!solution.empty()) break;
                    if (best > gbest || (best == gbest && bestcnt < gbcnt)) {
                        gbest = best; gbest_cur = best; gbcnt = (double)bestcnt;
                        gbestcert.clear(); for (int b : bestpath) gbestcert += char('0' + b);
                        int sh = 0;
                        for (int j = 1; j < POOL; j++)
                            if (pool[j].size() < pool[sh].size() || (pool[j].size() == pool[sh].size() && poolcnt[j] > poolcnt[sh])) sh = j;
                        pool[sh] = gbestcert; poolcnt[sh] = gbcnt;
                        again = true;
                    }
                }
            }
            if (!solution.empty()) {
                gbest = N - 1; gbestcert.clear(); for (int b : solution) gbestcert += char('0' + b);
                report();
                printf("CODE %d %s\n", n, gbestcert.c_str());
                fflush(stdout);
                return 0;
            }
        }
        double now = cpu_now();
        if (now - last > 1.0) { last = now; report(); }
    }
    report();
    fprintf(stderr, "NOTFOUND n=%d cpu=%.1fs moves=%llu best_words=%d/%d seed=%llu\n", n, cpu_now() - t0,
            (unsigned long long)moves, gbest + 1, N, (unsigned long long)seed);
    return 1;
}
