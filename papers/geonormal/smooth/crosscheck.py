"""Independent check of configs.py on configurations without tangencies or triple points.

For every tree with r = 8 + d vertices (networkx), 1 <= d <= 4, every choice of at most four vertices
of types (w, a) with a > 0 (the others being (-2)-curves, a = 0), and transversal intersections
along the edges, test whether A = -(E_i.E_j) is positive definite and A z = a has a solution
z >= 1 in integers with z.a = d.  Prints the determinants per (d, r); they should equal the
'simple-tree dets' printed by configs.py.  Runs in a few minutes on 16 cores.
"""
import itertools
from fractions import Fraction
from multiprocessing import Pool
import networkx as nx
import numpy as np
from configs import HEAVY, det


def exact_ok(A, a, d):
    """Exact confirmation: A positive definite and A^{-1} a a positive integer vector with z.a = d."""
    n = len(A)
    if not all(det([r[:k] for r in A[:k]]) > 0 for k in range(1, n + 1)): return False
    D = det(A)
    z = [Fraction(det([r[:i] + [a[k]] + r[i + 1:] for k, r in enumerate(A)]), D) for i in range(n)]
    return all(x.denominator == 1 and x >= 1 for x in z) and sum(x * y for x, y in zip(z, a)) == d


def tree_dets(args):
    d, edges, r = args
    out = set()
    for s in range(1, min(4, r) + 1):
        for S in itertools.combinations(range(r), s):
            for ty in itertools.product(HEAVY, repeat=s):
                if sum(t[1] for t in ty) > d: continue
                A = 2 * np.eye(r); a = np.zeros(r)
                for h, (w, x) in zip(S, ty): A[h, h] = w; a[h] = x
                for u, v in edges: A[u, v] = A[v, u] = -1
                # floating-point filter with loose tolerances, confirmed exactly below
                if np.linalg.eigvalsh(A).min() <= -1e-6: continue
                z = np.linalg.lstsq(A, a, rcond=None)[0]
                if (np.abs(z - np.round(z)) > 1e-3).any() or (np.round(z) < 1).any(): continue
                Ai = [[int(x) for x in row] for row in A]
                if exact_ok(Ai, [int(x) for x in a], d): out.add(det(Ai))
    return d, r, out


def main():
    tasks = []
    for d in range(1, 5):
        r = 8 + d
        tasks += [(d, list(T.edges()), r) for T in nx.nonisomorphic_trees(r)]
    total = {}
    with Pool() as pool:
        for d, r, out in pool.imap_unordered(tree_dets, tasks, chunksize=4):
            total.setdefault((d, r), set()).update(out)
    for (d, r) in sorted(total):
        print(f'd={d} r={r}: simple-tree dets {sorted(total[(d, r)])}')


if __name__ == '__main__':
    main()
