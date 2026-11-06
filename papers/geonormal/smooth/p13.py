"""Exceptional configurations relevant to Proposition prop:p13-sing.

All exceptional curves lie over the non-rational point, so r = 8+d.
Run the exact search of configs.py for det A in {13, 13^3}.
Degrees 1, 2 and 3 give no configurations. The degree-4 configuration is
printed for comparison with the tangent-cone obstruction in the proof.
"""
import itertools
import os
from multiprocessing import get_context

import networkx as nx

import configs

TARGETS = {13, 13**3}


def run_task(task):
    d, r, root, zroot = task
    found = []

    def out(A, z, mult):
        if configs.det(A) in TARGETS:
            found.append(([row[:] for row in A], list(z)))

    configs.search(d, r, [[root[0], root[1], zroot]], {}, [0], 0, out)
    return d, r, found


def graph(A, z):
    n = len(A)
    a = [sum(A[i][j] * z[j] for j in range(n)) for i in range(n)]
    G = nx.Graph()
    for i in range(n):
        G.add_node(i, w=A[i][i], a=a[i], z=z[i])
    for i, j in itertools.combinations(range(n), 2):
        if A[i][j]:
            G.add_edge(i, j, m=-A[i][j])
    return G, a


def main():
    tasks = [(d, 8+d, t, z) for d in range(1, 5)
             for t in configs.HEAVY for z in range(1, d // t[1] + 1)]
    total = {}
    # Fork avoids the Unix-domain socket needed by Python 3.14's forkserver.
    with get_context("fork").Pool(processes=min(8, os.cpu_count() or 1)) as pool:
        for d, r, found in pool.imap_unordered(run_task, tasks):
            total.setdefault((d, r), []).extend(found)
    for (d, r) in sorted(total):
        classes = []
        for A, z in total[(d, r)]:
            G, a = graph(A, z)
            assert all(zi >= 1 for zi in z) and all(ai >= 0 for ai in a)
            assert sum(ai * zi for ai, zi in zip(a, z)) == d
            assert all(configs.det([row[:k] for row in A[:k]]) > 0
                       for k in range(1, r+1))
            if not any(nx.is_isomorphic(G, H, node_match=lambda x, y: x == y,
                                        edge_match=lambda x, y: x == y)
                       for H, _, _, _ in classes):
                classes.append((G, A, z, a))
        print(f'd={d} r={r}: {len(classes)} configuration(s) with det A in {sorted(TARGETS)}')
        for G, A, z, a in classes:
            print(f'  det {configs.det(A)}: (w,a) {[(A[i][i], a[i]) for i in range(r)]}')
            print(f'    z {z}')
            print(f'    edges (i, j, E_i.E_j) {[(i, j, G.edges[i, j]["m"]) for i, j in G.edges]}')
        if d <= 3:
            assert not classes, f'Unexpected configuration in degree {d}'
        else:
            assert len(classes) == 1
            assert sum(ai > 0 for ai in classes[0][3]) == 2


if __name__ == '__main__':
    main()
