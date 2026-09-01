#!/usr/bin/env python3
"""Leftover graph of a uniform random independent set.

Let I be uniform in I(G). A vertex v is addable if I misses N[v]; write F for
the set of addable vertices. At λ=1, P(v addable)=P(v in I), so E[|F|]=E[|I|].
Any independent set of G[F] can be added to I, hence

    α(G) ≥ |I| + α(G[F])

in every realisation. If E[α(G[F])] ≥ δ E[|I|] for some δ>0 independent of G,
that would improve Shearer's leading constant. Caro–Wei on G[F] gives the
same conclusion whenever leftover degrees are O(1).
"""
from itertools import combinations


def leftover_from_masks(n, adj, isets):
    """isets: list of (mask, size). Return dict of averages."""
    z = len(isets)
    sum_size = 0
    sum_f = 0
    sum_alpha_f = 0
    sum_caro = 0
    sum_edges_f = 0
    sum_maxdeg_f = 0
    sum_avgdeg_f = 0
    n_with_f = 0
    deg = [adj[v].bit_count() for v in range(n)]

    closed = [(1 << v) | adj[v] for v in range(n)]
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if adj[u] & (1 << v)]

    for mask, sz in isets:
        sum_size += sz
        fmask = 0
        for v in range(n):
            if (closed[v] & mask) == 0:
                fmask |= 1 << v
        fn = fmask.bit_count()
        sum_f += fn
        if fn == 0:
            continue
        n_with_f += 1
        # leftover degrees
        maxd = 0
        sumd = 0
        ecount = 0
        caro = 0.0
        for v in range(n):
            if not (fmask & (1 << v)):
                continue
            d_f = (adj[v] & fmask).bit_count()
            maxd = max(maxd, d_f)
            sumd += d_f
            caro += 1.0 / (d_f + 1)
        ecount = sumd // 2
        sum_edges_f += ecount
        sum_maxdeg_f += maxd
        sum_avgdeg_f += (sumd / fn)
        sum_caro += caro
        # α(G[F]) by brute force on F (fn is small on typical I).
        # Empty I gives F=V; use Caro–Wei as a lower bound there only.
        alpha_f = 0
        verts = [v for v in range(n) if fmask & (1 << v)]
        m = len(verts)
        if 0 < m <= 18:
            for local in range(1 << m):
                ok = True
                g = 0
                for i in range(m):
                    if local & (1 << i):
                        if adj[verts[i]] & g:
                            ok = False
                            break
                        g |= 1 << verts[i]
                if ok:
                    alpha_f = max(alpha_f, local.bit_count())
        else:
            alpha_f = max(int(caro), 1 if m else 0)
        sum_alpha_f += alpha_f

    avg_i = sum_size / z
    avg_f = sum_f / z
    return {
        "z": z,
        "E|I|": avg_i,
        "E|F|": avg_f,
        "E α(F)": sum_alpha_f / z,
        "E CaroWei(F)": sum_caro / z,
        "E α(F) / E|I|": (sum_alpha_f / z) / avg_i if avg_i else None,
        "E Caro / E|I|": (sum_caro / z) / avg_i if avg_i else None,
        "E maxdeg(F)": sum_maxdeg_f / z,
        "E avgdeg(F | F≠∅)": (sum_avgdeg_f / n_with_f) if n_with_f else 0,
        "E e(F)": sum_edges_f / z,
        "mean leftover deg 2e/E|F|": (2 * sum_edges_f / z) / avg_f if avg_f else 0,
        "mean d(G)": sum(deg) / n,
    }


def all_isets(n, adj):
    out = []
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
            out.append((mask, mask.bit_count()))
    return out


def adj_from_edges(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def circulant_adj(n, distances):
    adj = [0] * n
    S = set()
    for d in distances:
        S.add(d % n)
        S.add((-d) % n)
    S.discard(0)
    for i in range(n):
        for d in S:
            adj[i] |= 1 << ((i + d) % n)
    return adj


def list_circulant_isets(n, adj):
    """Meet-in-the-middle listing of all independent sets of a circulant."""
    mid = n // 2
    left = list(range(mid))
    right = list(range(mid, n))

    def isets_on(verts):
        m = len(verts)
        out = []
        for local in range(1 << m):
            gmask = 0
            ok = True
            sz = 0
            for i in range(m):
                if local & (1 << i):
                    v = verts[i]
                    if adj[v] & gmask:
                        ok = False
                        break
                    gmask |= 1 << v
                    sz += 1
            if ok:
                out.append((gmask, sz))
        return out

    LIS = isets_on(left)
    RIS = isets_on(right)
    out = []
    for gL, szL in LIS:
        forbidden = 0
        m = gL
        while m:
            v = (m & -m).bit_length() - 1
            forbidden |= adj[v]
            m &= m - 1
        for gR, szR in RIS:
            if gR & forbidden:
                continue
            out.append((gL | gR, szL + szR))
    return out


def named():
    graphs = {}
    graphs["K1"] = (1, adj_from_edges(1, []))
    graphs["K2"] = (2, adj_from_edges(2, [(0, 1)]))
    graphs["2K2"] = (4, adj_from_edges(4, [(0, 1), (2, 3)]))
    graphs["C4"] = (4, adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)]))
    graphs["C5"] = (5, circulant_adj(5, [1]))
    graphs["C7"] = (7, circulant_adj(7, [1]))
    pet = []
    for i in range(5):
        pet.append((i, (i + 1) % 5))
        pet.append((i, i + 5))
        pet.append((i + 5, ((i + 2) % 5) + 5))
    graphs["Petersen"] = (10, adj_from_edges(10, pet))
    cleb = []
    for i in range(16):
        for j in range(i + 1, 16):
            w = (i ^ j).bit_count()
            if w in (1, 4):
                cleb.append((i, j))
    graphs["Clebsch-like"] = (16, adj_from_edges(16, cleb))
    # Chvátal: 12 vertices 4-regular, triangle-free, α=4
    # circulant C12(1,5)
    graphs["Chvatal"] = (12, circulant_adj(12, [1, 5]))
    return graphs


def main():
    print(
        f"{'graph':<16} {'n':>3} {'d':>4} {'E|I|':>7} {'E|F|':>7} "
        f"{'EαF':>7} {'ratio':>7} {'Caro':>7} {'d_F':>7} {'maxdF':>7}"
    )
    for name, (n, adj) in named().items():
        isets = all_isets(n, adj)
        st = leftover_from_masks(n, adj, isets)
        print(
            f"{name:<16} {n:3d} {st['mean d(G)']:4.1f} {st['E|I|']:7.3f} "
            f"{st['E|F|']:7.3f} {st['E α(F)']:7.3f} {st['E α(F) / E|I|']:7.3f} "
            f"{st['E Caro / E|I|']:7.3f} {st['mean leftover deg 2e/E|F|']:7.3f} "
            f"{st['E maxdeg(F)']:7.3f}"
        )

    print("\nKalbfleisch C35 listing independent sets...", flush=True)
    n = 35
    adj = circulant_adj(n, [1, 7, 11, 16])
    isets = list_circulant_isets(n, adj)
    st = leftover_from_masks(n, adj, isets)
    print("Kalbfleisch z", st["z"], "expected 73926")
    for k, v in st.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
