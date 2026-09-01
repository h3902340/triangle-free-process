#!/usr/bin/env python3
"""Scan α / α_G(1) on small triangle-free graphs. DJPR Conjecture 1 is ≥ 4/3."""
from itertools import combinations
import random


def is_triangle_free(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    for u, v in edges:
        if adj[u] & adj[v]:
            return False
    return True


def independence_stats(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    z = 0
    size_sum = 0
    alpha = 0
    for mask in range(1 << n):
        ok = True
        m = mask
        while m:
            v = (m & -m).bit_length() - 1
            if adj[v] & mask:
                ok = False
                break
            m &= m - 1
        if ok:
            sz = mask.bit_count()
            z += 1
            size_sum += sz
            if sz > alpha:
                alpha = sz
    avg = size_sum / z
    return alpha, avg, alpha / avg, z


def named_graphs():
    graphs = {}
    # empty n=1
    graphs["K1"] = (1, [])
    # single edge
    graphs["K2"] = (2, [(0, 1)])
    # matching 2 edges
    graphs["2K2"] = (4, [(0, 1), (2, 3)])
    # C5
    graphs["C5"] = (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
    # C4
    graphs["C4"] = (4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    # Petersen
    pet = []
    for i in range(5):
        pet.append((i, (i + 1) % 5))
        pet.append((i, i + 5))
        pet.append((i + 5, ((i + 2) % 5) + 5))
    graphs["Petersen"] = (10, pet)
    # Clebsch: 16 vertices, 5-regular, triangle-free. Complement of 4-cube's
    # 5-bit vectors, edges when Hamming distance 2? Standard: vertices F_2^4,
    # edges Hamming distance 3? Clebsch = 5-regular on 16 verts.
    # Vertices: 0..15. Connect i~j if popcount(i xor j)==2? That's 4-cube
    # complement pieces. The 5-cube folded: connect if popcount(xor) in {1,4}
    # One construction: 16 vertices of 4-dim cube + connections.
    # Use: vertices F_2^4, edge iff Hamming weight of xor is 1 or 4.
    cleb = []
    for i in range(16):
        for j in range(i + 1, 16):
            w = (i ^ j).bit_count()
            if w in (1, 4):
                cleb.append((i, j))
    graphs["Clebsch-like"] = (16, cleb)
    return graphs


def random_triangle_free(n, p, tries=200):
    found = []
    for _ in range(tries):
        edges = [(i, j) for i, j in combinations(range(n), 2) if random.random() < p]
        if is_triangle_free(n, edges) and edges:
            found.append(edges)
            if len(found) >= 8:
                break
    return found


def main():
    print(f"{'graph':<22} {'n':>3} {'α':>3} {'avg':>8} {'ratio':>8} {'z':>8}")
    worst = (10, None, None)
    for name, (n, edges) in named_graphs().items():
        if not is_triangle_free(n, edges):
            print(f"{name:<22} NOT triangle-free")
            continue
        a, avg, r, z = independence_stats(n, edges)
        print(f"{name:<22} {n:3d} {a:3d} {avg:8.4f} {r:8.4f} {z:8d}")
        if r < worst[0]:
            worst = (r, name, n)

    random.seed(0)
    for n in range(6, 13):
        p = 1.5 / n
        for idx, edges in enumerate(random_triangle_free(n, p)):
            a, avg, r, z = independence_stats(n, edges)
            tag = f"rnd n={n} #{idx}"
            if r < 1.5:
                print(f"{tag:<22} {n:3d} {a:3d} {avg:8.4f} {r:8.4f} {z:8d}")
            if r < worst[0]:
                worst = (r, tag, n)

    print("worst seen:", worst)
    print("4/3 =", 4 / 3)


if __name__ == "__main__":
    main()
