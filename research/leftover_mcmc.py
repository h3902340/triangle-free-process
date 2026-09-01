#!/usr/bin/env python3
"""Glauber dynamics for leftover-degree of the hard-core model at λ=1.

Used to test whether leftover average degree stays O(1) as d grows.
If it does, Caro–Wei on the leftover graph would give α ≥ (1+δ) α_G(1)
and a leading-constant improvement of Shearer.
"""
import random
import time


def hoffman_singleton():
    """Robertson pentagon/pentagram construction. n=50, d=7, triangle-free."""
    # vertices: pentagon (0,h,j) and pentagram (1,i,j), h,i,j in Z_5
    def vid(kind, a, b):
        return kind * 25 + a * 5 + b

    n = 50
    adj = [[] for _ in range(n)]

    def add(u, v):
        adj[u].append(v)
        adj[v].append(u)

    for i in range(5):
        for j in range(5):
            add(vid(0, i, j), vid(0, i, (j - 1) % 5))
            add(vid(1, i, j), vid(1, i, (j - 2) % 5))
            for k in range(5):
                add(vid(0, i, j), vid(1, k, (i * k + j) % 5))
    # unique-ify
    adj = [sorted(set(nbrs)) for nbrs in adj]
    return n, adj


def config_regular(n, d, seed=0):
    """Configuration model with local stub repairs."""
    rng = random.Random(seed)
    stubs = []
    for v in range(n):
        stubs.extend([v] * d)
    for _ in range(5000):
        rng.shuffle(stubs)
        adj_set = [set() for _ in range(n)]
        ok = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v or v in adj_set[u]:
                ok = False
                break
            adj_set[u].add(v)
            adj_set[v].add(u)
        if ok:
            return n, [sorted(s) for s in adj_set]
    raise RuntimeError("failed to sample simple regular graph")


def triangle_free_process(n, seed=0):
    """Random permutation of pairs; keep an edge iff it creates no triangle."""
    rng = random.Random(seed)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rng.shuffle(pairs)
    adj_set = [set() for _ in range(n)]
    for u, v in pairs:
        if adj_set[u] & adj_set[v]:
            continue
        adj_set[u].add(v)
        adj_set[v].add(u)
    return n, [sorted(s) for s in adj_set]


def lcf_graph(n, offsets):
    """Cubic Hamiltonian graph from LCF offsets (length n)."""
    adj = [set() for _ in range(n)]
    for i in range(n):
        adj[i].add((i + 1) % n)
        adj[i].add((i - 1) % n)
        adj[i].add((i + offsets[i]) % n)
    return n, [sorted(s) for s in adj]


def triangle_count(adj):
    t = 0
    for v, nbrs in enumerate(adj):
        s = set(nbrs)
        for i, u in enumerate(nbrs):
            if u < v:
                continue
            t += sum(1 for w in nbrs[i + 1 :] if w in s and w in [x for x in adj[u]])
        # slower but fine
    # recount carefully
    t = 0
    for v, nbrs in enumerate(adj):
        ns = set(nbrs)
        for u in nbrs:
            if u <= v:
                continue
            t += sum(1 for w in adj[u] if w > u and w in ns)
    return t


def delete_triangles(adj):
    """Delete one edge from each triangle (greedy). Remaining is triangle-free."""
    n = len(adj)
    s = [set(nbrs) for nbrs in adj]
    changed = True
    while changed:
        changed = False
        for v in range(n):
            nbrs = list(s[v])
            ns = s[v]
            for i, u in enumerate(nbrs):
                for w in nbrs[i + 1 :]:
                    if w in s[u]:
                        # delete uw
                        s[u].discard(w)
                        s[w].discard(u)
                        changed = True
                        break
                if changed:
                    break
            if changed:
                break
    return [sorted(x) for x in s]


def mean_degree(adj):
    return sum(len(a) for a in adj) / len(adj)


def seed_greedy(adj, rng):
    n = len(adj)
    occupied = [False] * n
    occ_count = [0] * n
    size = 0
    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if occ_count[v] == 0:
            occupied[v] = True
            size += 1
            for u in adj[v]:
                occ_count[u] += 1
    return occupied, occ_count, size


def glauber_leftover(adj, steps, burn, seed=0, record_every=50, greedy_start=True):
    rng = random.Random(seed)
    n = len(adj)
    nbr = [set(a) for a in adj]
    if greedy_start:
        occupied, occ_count, size = seed_greedy(adj, rng)
        # mix from a maximal set by removing a few
        for _ in range(n):
            v = rng.randrange(n)
            if occupied[v]:
                occupied[v] = False
                size -= 1
                for u in nbr[v]:
                    occ_count[u] -= 1
    else:
        occupied = [False] * n
        occ_count = [0] * n
        size = 0
    samples = 0
    sum_size = 0.0
    sum_f = 0.0
    sum_e_f = 0.0
    sum_caro = 0.0
    sum_maxd = 0.0

    def addable(v):
        return (not occupied[v]) and occ_count[v] == 0

    for t in range(steps):
        v = rng.randrange(n)
        if occupied[v]:
            if rng.random() < 0.5:
                occupied[v] = False
                size -= 1
                for u in nbr[v]:
                    occ_count[u] -= 1
        else:
            if occ_count[v] == 0 and rng.random() < 0.5:
                occupied[v] = True
                size += 1
                for u in nbr[v]:
                    occ_count[u] += 1
        if t >= burn and (t - burn) % record_every == 0:
            f = [x for x in range(n) if addable(x)]
            fn = len(f)
            fset = set(f)
            e_f = 0
            maxd = 0
            caro = 0.0
            for x in f:
                df = sum(1 for y in nbr[x] if y in fset)
                e_f += df
                maxd = max(maxd, df)
                caro += 1.0 / (df + 1)
            e_f //= 2
            samples += 1
            sum_size += size
            sum_f += fn
            sum_e_f += e_f
            sum_caro += caro
            sum_maxd += maxd
    avg_i = sum_size / samples
    avg_f = sum_f / samples
    d_f = (2 * sum_e_f / samples) / avg_f if avg_f else 0
    return {
        "samples": samples,
        "E|I|": avg_i,
        "E|F|": avg_f,
        "E CaroWei(F)": sum_caro / samples,
        "Caro/E|I|": (sum_caro / samples) / avg_i if avg_i else 0,
        "mean leftover deg": d_f,
        "E maxdeg(F)": sum_maxd / samples,
    }


def main():
    n, adj = hoffman_singleton()
    degs = [len(a) for a in adj]
    assert all(d == 7 for d in degs), degs[:10]
    assert triangle_count(adj) == 0
    print("Hoffman-Singleton n=50 d=7 triangles=0")
    t0 = time.time()
    st = glauber_leftover(adj, steps=400_000, burn=50_000, seed=1, record_every=20)
    print(f"  {st}  ({time.time()-t0:.1f}s)")

    print("\nNamed cages (LCF):")
    cages = {
        "Heawood": (14, [5, -5] * 7),
        "McGee": (24, [12, 7, -7] * 8),
        "Nauru": (24, [5, -9, 7, -7, 9, -5] * 4),
        "Tutte-Coxeter": (30, [-13, -9, 7, -7, 9, 13] * 5),
    }
    for name, (n, offs) in cages.items():
        _, adj = lcf_graph(n, offs)
        md = mean_degree(adj)
        tri = triangle_count(adj)
        t0 = time.time()
        st = glauber_leftover(adj, steps=250_000, burn=30_000, seed=2, record_every=20)
        print(
            f"  {name} n={n} d={md:.1f} tri={tri} "
            f"d_F={st['mean leftover deg']:.3f} Caro/μ={st['Caro/E|I|']:.3f} "
            f"E|I|={st['E|I|']:.2f} ({time.time()-t0:.1f}s)"
        )

    print("\nTriangle-free process:")
    for n, seed in [
        (30, 0),
        (40, 1),
        (50, 2),
        (70, 3),
        (90, 4),
        (120, 5),
        (200, 6),
        (400, 7),
        (800, 8),
    ]:
        t1 = time.time()
        _, adj = triangle_free_process(n, seed=seed)
        md = mean_degree(adj)
        steps = max(400_000, 8 * n * n)
        burn = steps // 8
        st = glauber_leftover(
            adj, steps=steps, burn=burn, seed=seed + 20, record_every=max(20, n // 5)
        )
        print(
            f"  n={n} d={md:.2f} "
            f"d_F={st['mean leftover deg']:.3f} Caro/μ={st['Caro/E|I|']:.3f} "
            f"E|I|={st['E|I|']:.2f} E|F|={st['E|F|']:.2f} maxdF={st['E maxdeg(F)']:.2f} "
            f"({time.time()-t1:.1f}s)"
        )


if __name__ == "__main__":
    main()
