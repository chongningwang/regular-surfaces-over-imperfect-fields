"""Exceptional configurations over the non-rational singular point y_0 (Section sec:smooth).

Enumerates all matrices A = -(E_i.E_j) of configurations E_0 = E_1 + ... + E_r satisfying the
conditions of Lemma lem:smooth-config:
  * each E_i is a rational curve with w = -E_i^2 >= 1, a = K.E_i >= 0, a = w - 2 + 2 p_a(E_i);
  * the incidence graph of curves and points lying on at least two curves is a tree, a point lies
    on at most three curves, of which at most two are (-2)-curves, and two curves meeting at a
    point with local intersection number m satisfy m^2 < w w';
  * A is positive definite, and A z = a for a vector z of positive integers with z.a = d <= 4;
  * r = 8 + d, with 1 <= d <= 4.
A configuration is grown from a curve with a > 0 by breadth-first search: the balance
w_v z_v - a_v = sum_u z_u (E_u.E_v) of each curve v is split between the point joining v to its
parent and the points joining v to its children.  Duplicates are harmless.

Output: the determinants that occur (also those of configurations without tangencies or triple
points, for comparison with crosscheck.py), and the primes p >= 29 occurring as det A, with all
their configurations up to isomorphism (Proposition prop:smooth-enum).
Runs in under a minute.
"""
import itertools
from multiprocessing import Pool
import networkx as nx
from sympy import isprime

HEAVY = [(w, a) for a in range(1, 5) for w in range(a % 2 or 2, a + 3, 2)]  # w = a+2-2p_a >= 1
LIGHT = (2, 0)
TYPES = HEAVY + [LIGHT]
assert sorted(HEAVY) == sorted([(3, 1), (1, 1), (4, 2), (2, 2), (5, 3), (3, 3), (1, 3),
                                (6, 4), (4, 4), (2, 4)])


def det(M):
    """Exact determinant (Bareiss)."""
    n = len(M); A = [row[:] for row in M]; prev = 1; sign = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k]:
                    A[k], A[i] = A[i], A[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def matrix(nodes, mult):
    n = len(nodes)
    A = [[0] * n for _ in range(n)]
    for i in range(n): A[i][i] = nodes[i][0]
    for (i, j), m in mult.items(): A[i][j] = A[j][i] = -m
    return A


def child_options(wv, av, budget, maxnew, d):
    """Child points of a curve of type (wv, av): 1 or 2 new curves, with z, m to v, and m between
    the new curves; contribution to the balance of v is sum z*m <= budget."""
    opts = []
    for k in range(1, min(2, maxnew) + 1):
        for combo in itertools.combinations_with_replacement(range(len(TYPES)), k):
            ts = [TYPES[t] for t in combo]
            if sum(t[1] == 0 for t in ts) + (av == 0) > 2: continue
            per = [[(z, m) for m in range(1, 4) if m * m < w * wv
                    for z in range(1, budget // m + 1) if a * z <= d] for (w, a) in ts]
            for zm in itertools.product(*per):
                if k == 2 and combo[0] == combo[1] and zm[0] > zm[1]: continue
                contrib = sum(z * m for z, m in zm)
                if contrib > budget: continue
                pms = [[()]] if k == 1 else [[(m,) for m in range(1, 4) if m * m < ts[0][0] * ts[1][0]]]
                for (pm,) in itertools.product(*pms):
                    opts.append((contrib, tuple(ts), zm, pm))
    opts.sort()
    return opts


def search(d, R, nodes, mult, parentc, v, out):
    """Process curves v, v+1, ... ; nodes[i] = [w, a, z]."""
    cache = {}

    def posdef_tail(n0):
        A = matrix(nodes, mult)
        return all(det([r[:k] for r in A[:k]]) > 0 for k in range(n0 + 1, len(A) + 1))

    def expand(v):
        if v == len(nodes):
            if len(nodes) == R and sum(x[1] * x[2] for x in nodes) == d:
                out(matrix(nodes, mult), [x[2] for x in nodes], mult)
            return
        w, a, z = nodes[v]
        delta = w * z - a - parentc[v]
        if delta < 0: return
        key = (w, a, delta, R - len(nodes))
        if key not in cache: cache[key] = child_options(w, a, delta, R - len(nodes), d)
        opts = cache[key]

        def choose(start, remaining):
            if remaining == 0:
                expand(v + 1); return
            for idx in range(start, len(opts)):
                contrib, ts, zm, pm = opts[idx]
                if contrib > remaining: break
                k = len(ts); base = len(nodes)
                if base + k > R: continue
                for t, (zz, m) in zip(ts, zm):
                    nodes.append([t[0], t[1], zz]); parentc.append(0)
                new = list(range(base, base + k))
                for i, (zz, m) in zip(new, zm): mult[(v, i)] = m
                if k == 2: mult[(base, base + 1)] = pm[0]
                if sum(x[1] * x[2] for x in nodes) <= d and posdef_tail(base):
                    pt = [v] + new
                    for i in new:
                        parentc[i] = sum(nodes[j][2] * mult[(min(i, j), max(i, j))] for j in pt if j != i)
                    choose(idx, remaining - contrib)
                for i in new: del mult[(v, i)]
                if k == 2: del mult[(base, base + 1)]
                del nodes[base:]; del parentc[base:]
        choose(0, delta)

    expand(v)


def run_task(task):
    d, R, root, zroot = task
    res = {}  # det -> [list of (A, z) if det is a prime >= 29, simple?]

    def out(A, z, mult):
        D = det(A)
        simple = all(m == 1 for m in mult.values()) and not any(
            (i, j) in mult and (i, k) in mult and (j, k) in mult
            for i, j, k in itertools.combinations(range(len(A)), 3))
        e = res.setdefault(D, [[], False])
        e[1] |= simple
        if D >= 29 and isprime(D): e[0].append((A, z))

    search(d, R, [[root[0], root[1], zroot]], {}, [0], 0, out)
    return d, R, res


def main():
    tasks = [(d, 8 + d, t, z) for d in range(1, 5)
             for t in HEAVY for z in range(1, d // t[1] + 1)]
    total = {}
    with Pool() as pool:
        for d, R, res in pool.imap_unordered(run_task, tasks):
            T = total.setdefault((d, R), {})
            for D, (ex, simple) in res.items():
                e = T.setdefault(D, [[], False])
                e[0] += ex; e[1] |= simple
    S = set()
    for (d, R) in sorted(total):
        T = total[(d, R)]
        print(f'd={d} r={R}: dets {sorted(T)}')
        print(f'    simple-tree dets {sorted(D for D in T if T[D][1])}')
        assert max(T) <= 2**8 * 3**d
        for D in sorted(T):
            if T[D][0]:
                S.add(D); classes = []
                for A, z in T[D][0]:
                    G = nx.Graph()
                    for i in range(len(A)): G.add_node(i, w=A[i][i])
                    for i, j in itertools.combinations(range(len(A)), 2):
                        if A[i][j]: G.add_edge(i, j, m=-A[i][j])
                    if not any(nx.is_isomorphic(G, H, node_match=lambda x, y: x == y,
                                                edge_match=lambda x, y: x == y) for H, _ in classes):
                        classes.append((G, z))
                print(f'    prime {D}: {len(classes)} configuration(s) up to isomorphism')
                for G, z in classes:
                    print(f'      diagonal {[G.nodes[i]["w"] for i in G]}, z {z},')
                    print(f'      edges (i, j, E_i.E_j) {[(i, j, G.edges[i, j]["m"]) for i, j in G.edges]}')
    print('primes >= 29 occurring as det A:', sorted(S))


if __name__ == '__main__':
    main()
