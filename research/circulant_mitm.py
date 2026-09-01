#!/usr/bin/env python3
"""Meet-in-the-middle independence polynomial for a circulant graph."""


def build_adj(n, distances):
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


def independent_sets(verts, adj):
    """verts: list of vertex indices. Return list of (bitmask_on_local_order, size, global_mask)."""
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
            out.append((local, sz, gmask))
    return out


def sos_from_list(m, items):
    """items: (local_mask, size). Return arrays count[U], size_sum[U] summed over IS contained in U."""
    N = 1 << m
    count = [0] * N
    ssum = [0] * N
    for mask, sz in items:
        count[mask] += 1
        ssum[mask] += sz
    for i in range(m):
        bit = 1 << i
        for u in range(N):
            if u & bit:
                count[u] += count[u ^ bit]
                ssum[u] += ssum[u ^ bit]
    return count, ssum


def stats(n, distances):
    adj = build_adj(n, distances)
    mid = n // 2
    left = list(range(mid))
    right = list(range(mid, n))
    LIS = independent_sets(left, adj)
    RIS = independent_sets(right, adj)
    r_items = [(local, sz) for local, sz, _ in RIS]
    # map right global vertex -> local bit
    r_index = {v: j for j, v in enumerate(right)}
    mR = len(right)
    count, ssum = sos_from_list(mR, r_items)

    z = 0
    size_sum = 0
    alpha = 0
    # also track max: SOS doesn't give max. Compute alpha separately via listing
    # For each left, allowed right local mask, max independent set in induced on allowed
    # We can store maxsz[mask] for each right IS, then SOS max
    maxsz = [0] * (1 << mR)
    for local, sz in r_items:
        if sz > maxsz[local]:
            maxsz[local] = sz
    for i in range(mR):
        bit = 1 << i
        for u in range(1 << mR):
            if u & bit:
                if maxsz[u ^ bit] > maxsz[u]:
                    maxsz[u] = maxsz[u ^ bit]

    for local, szL, gL in LIS:
        forbidden = 0
        m = gL
        while m:
            v = (m & -m).bit_length() - 1
            nbrs = adj[v]
            # right neighbors
            rbits = 0
            nb = nbrs
            while nb:
                w = (nb & -nb).bit_length() - 1
                if w in r_index:
                    rbits |= 1 << r_index[w]
                nb &= nb - 1
            forbidden |= rbits
            m &= m - 1
        allowed = ((1 << mR) - 1) ^ forbidden
        z += count[allowed]
        size_sum += szL * count[allowed] + ssum[allowed]
        alpha = max(alpha, szL + maxsz[allowed])
    avg = size_sum / z
    return alpha, avg, alpha / avg, z


def main():
    print("C5", stats(5, [1]))
    print("C4", stats(4, [1]))
    print("C7", stats(7, [1]))
    print("Kalbfleisch...", flush=True)
    print("Kalbfleisch", stats(35, [1, 7, 11, 16]))
    print("DJPR", 197136 / 137585)


if __name__ == "__main__":
    main()
