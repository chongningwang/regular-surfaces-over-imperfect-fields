"""Exceptional configurations with det A a power of 17 (Proposition prop:small-primes-sing).

Runs the search of configs.py unchanged and keeps the matrices A with det A in {17, 17^3}, the
odd powers of 17 allowed by Proposition prop:smooth-det.  For r = 8+d, 1 <= d <= 4, it prints these
configurations up to isomorphism, with the types (w_i, a_i) = (-E_i^2, K.E_i), the coefficients
z_i of Z = sum z_i E_i (so that A z = a) and the edges.
"""
import itertools
import os
import sys
from multiprocessing import Pool

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import configs  # noqa: E402

TARGETS = {17, 17**3}


def run_task(task):
    d, R, root, zroot = task
    found = []

    def out(A, z, mult):
        if configs.det(A) in TARGETS:
            found.append(([row[:] for row in A], list(z)))

    configs.search(d, R, [[root[0], root[1], zroot]], {}, [0], 0, out)
    return d, R, found


def graph(A):
    G = nx.Graph()
    for i in range(len(A)):
        G.add_node(i, w=A[i][i])
    for i, j in itertools.combinations(range(len(A)), 2):
        if A[i][j]:
            G.add_edge(i, j, m=-A[i][j])
    return G


def main():
    tasks = [(d, 8 + d, t, z) for d in range(1, 5)
             for t in configs.HEAVY for z in range(1, d // t[1] + 1)]
    total = {}
    with Pool() as pool:
        for d, R, found in pool.imap_unordered(run_task, tasks):
            total.setdefault((d, R), []).extend(found)
    for (d, R) in sorted(total):
        classes = []
        for A, z in total[(d, R)]:
            G = graph(A)
            if not any(nx.is_isomorphic(G, H, node_match=lambda x, y: x == y,
                                        edge_match=lambda x, y: x == y) for H, _, _ in classes):
                classes.append((G, A, z))
        print(f'd={d} r={R}: {len(classes)} configuration(s) with det A in {sorted(TARGETS)}')
        for G, A, z in classes:
            n = len(A)
            a = [sum(A[i][j] * z[j] for j in range(n)) for i in range(n)]
            assert sum(ai * zi for ai, zi in zip(a, z)) == d
            print(f'  det {configs.det(A)}: (w,a) {[(A[i][i], a[i]) for i in range(n)]}')
            print(f'    z {z}')
            print(f'    edges (i, j, E_i.E_j) {[(i, j, G.edges[i, j]["m"]) for i, j in G.edges]}')


if __name__ == '__main__':
    main()
