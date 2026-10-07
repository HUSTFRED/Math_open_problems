#!/usr/bin/env python3
"""Rebuild a fixed tree's independent-set counts using graph deletion.

Python standard library only. No old program, polynomial, expected
coefficient, supplied matching, or symbolic family formula is used.
Run: python3 check_tree90.py
"""

import argparse
from collections import deque
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import signal
import sys
import time


AS_LIMIT = 512 * 1024 * 1024
CPU_LIMIT_SECONDS = 120
FIXED_VERTEX_COUNT = 90


def require(condition, message):
    if not condition:
        raise ValueError(message)


def wall_alarm(signum, frame):
    raise TimeoutError("120-second wall-clock limit exceeded")


def configure_limits():
    resource.setrlimit(resource.RLIMIT_AS, (AS_LIMIT, AS_LIMIT))
    resource.setrlimit(resource.RLIMIT_CPU,
                       (CPU_LIMIT_SECONDS, CPU_LIMIT_SECONDS))
    available = os.sched_getaffinity(0)
    require(bool(available), "empty CPU affinity")
    os.sched_setaffinity(0, {min(available)})
    signal.signal(signal.SIGALRM, wall_alarm)
    signal.alarm(CPU_LIMIT_SECONDS)


def validate_graph(data):
    require(set(data) == {"N", "edges"},
            "input must contain only N and edges")
    n = data["N"]
    require(type(n) is int and n == FIXED_VERTEX_COUNT,
            "this reproduction is restricted to N=90")
    require(type(data["edges"]) is list, "edges must be a list")
    adjacency = [set() for _ in range(n)]
    edges = []
    seen = set()
    for entry in data["edges"]:
        require(type(entry) is list and len(entry) == 2,
                "each edge must have two vertices")
        u, v = entry
        require(type(u) is int and type(v) is int,
                "vertex labels must be integers")
        require(0 <= u < n and 0 <= v < n and u != v,
                "loop or vertex outside 0..N-1")
        edge = tuple(sorted((u, v)))
        require(edge not in seen, "duplicate undirected edge")
        seen.add(edge)
        edges.append(edge)
        adjacency[u].add(v)
        adjacency[v].add(u)

    parent = [-1] * n
    color = [-1] * n
    color[0] = 0
    queue = deque([0])
    reached = 0
    while queue:
        u = queue.popleft()
        reached += 1
        for v in sorted(adjacency[u]):
            if color[v] == -1:
                parent[v] = u
                color[v] = 1 - color[u]
                queue.append(v)
            else:
                require(v == parent[u] or u == parent[v],
                        "cycle detected")
                require(color[v] != color[u], "not bipartite")
    require(reached == n, "graph is not connected")
    require(len(edges) == n - 1, "wrong tree edge count")
    return n, sorted(edges), adjacency, color


def matching_and_cover(adjacency, edges):
    """Leaf exchange constructs a maximum matching and equal-size cover."""
    active = [set(neighbors) for neighbors in adjacency]
    remaining = set(range(len(active)))
    matching = []
    cover = []
    trace = []

    def remove(v):
        for w in tuple(active[v]):
            active[w].remove(v)
        active[v].clear()
        remaining.remove(v)

    while remaining:
        isolated = sorted(v for v in remaining if not active[v])
        if isolated:
            for v in isolated:
                trace.append({"isolated": v})
                remove(v)
            continue
        leaves = [v for v in remaining if len(active[v]) == 1]
        require(bool(leaves), "nonempty forest has no leaf")
        leaf = min(leaves)
        neighbor = next(iter(active[leaf]))
        matching.append(tuple(sorted((leaf, neighbor))))
        cover.append(neighbor)
        trace.append({"leaf": leaf, "matched_neighbor": neighbor})
        remove(leaf)
        remove(neighbor)

    edge_set = set(edges)
    used = set()
    for u, v in matching:
        require((u, v) in edge_set, "matching uses a nonedge")
        require(u not in used and v not in used,
                "matching edges are not disjoint")
        used.update((u, v))
    cover_set = set(cover)
    require(len(cover_set) == len(matching), "cover has wrong size")
    require(all(u in cover_set or v in cover_set for u, v in edges),
            "computed cover does not cover every edge")
    independent = sorted(set(range(len(active))) - cover_set)
    independent_set = set(independent)
    require(all(not (u in independent_set and v in independent_set)
                for u, v in edges), "witness is not independent")
    require(len(used) == len(active), "this graph lacks the found perfect matching")
    require(len(independent) == len(matching),
            "perfect-matching independence upper bound not attained")
    return sorted(matching), sorted(cover), independent, trace


def multiply(left, right):
    product = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product[i + j] += a * b
    return tuple(product)


def rebuild_polynomial(adjacency):
    """Deletion / closed-neighborhood deletion, plus component products."""
    n = len(adjacency)
    neighbors = [sum(1 << v for v in row) for row in adjacency]
    statistics = {"component_factorizations": 0,
                  "vertex_deletion_splits": 0}

    def components(mask):
        remaining = mask
        result = []
        while remaining:
            frontier = remaining & -remaining
            component = 0
            while frontier:
                bit = frontier & -frontier
                frontier ^= bit
                if component & bit:
                    continue
                component |= bit
                v = bit.bit_length() - 1
                frontier |= neighbors[v] & mask & ~component
            result.append(component)
            remaining &= ~component
        return result

    @lru_cache(maxsize=None)
    def polynomial(mask):
        if mask == 0:
            return (1,)
        parts = components(mask)
        if len(parts) > 1:
            statistics["component_factorizations"] += 1
            product = (1,)
            for part in parts:
                product = multiply(product, polynomial(part))
            return product
        if mask.bit_count() == 1:
            return (1, 1)

        candidates = []
        remaining = mask
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            v = bit.bit_length() - 1
            candidates.append(((neighbors[v] & mask).bit_count(), -v, v))
        v = max(candidates)[2]
        bit = 1 << v
        without_v = mask & ~bit
        without_closed_neighborhood = without_v & ~neighbors[v]
        statistics["vertex_deletion_splits"] += 1
        excluded = polynomial(without_v)
        included = polynomial(without_closed_neighborhood)
        result = [0] * max(len(excluded), len(included) + 1)
        for k, value in enumerate(excluded):
            result[k] += value
        for k, value in enumerate(included):
            result[k + 1] += value
        return tuple(result)

    coefficients = polynomial((1 << n) - 1)
    statistics["memoization"] = polynomial.cache_info()._asdict()
    return coefficients, statistics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", nargs="?", type=Path,
                        default=Path(__file__).with_name("tree90_edges.json"))
    args = parser.parse_args()
    start = time.perf_counter()
    configure_limits()
    source = Path(__file__).resolve()
    raw_input = args.graph.read_bytes()
    data = json.loads(raw_input)
    n, edges, adjacency, color = validate_graph(data)
    matching, cover, independent, trace = matching_and_cover(adjacency, edges)
    coefficients, statistics = rebuild_polynomial(adjacency)
    nu = len(matching)
    alpha = len(independent)
    require(len(coefficients) - 1 == alpha,
            "polynomial degree disagrees with independent-set witness")
    require(all(type(x) is int and x > 0 for x in coefficients),
            "coefficient support has a gap or a noninteger")
    require(coefficients[0] == 1 and coefficients[1] == n,
            "empty-set or singleton coefficient check failed")
    require(coefficients[2] == n * (n - 1) // 2 - len(edges),
            "independent pair coefficient check failed")

    h = n // 2
    q = n - 2 * h
    j = nu - 1
    beta = h - j
    require(1 <= j <= nu - q and beta >= 0,
            "index is outside the explicit RS4.2 target")
    left, center, right = coefficients[j-1:j+2]
    difference = center * center - left * right
    required_alpha = h + beta + 1
    failed_target = difference < 0 and alpha < required_alpha
    usage = resource.getrusage(resource.RUSAGE_SELF)
    result = {
        "schema": "RS42-INDEPENDENT-GRAPH-DELETION-v1",
        "input_sha256": hashlib.sha256(raw_input).hexdigest(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "interpreter": {"executable": sys.executable,
                        "version": sys.version,
                        "implementation": platform.python_implementation()},
        "algorithm": "memoized induced vertex deletion and component factorization",
        "N": n, "edge_count": len(edges),
        "graph_checks": {"simple": True, "connected": True,
                         "acyclic": True, "bipartite": True},
        "matching": matching, "vertex_cover": cover,
        "maximum_independent_set": independent,
        "leaf_elimination_trace": trace,
        "bipartition": [[v for v in range(n) if color[v] == c] for c in (0, 1)],
        "nu": nu, "alpha": alpha,
        "full_coefficients": list(coefficients),
        "h": h, "q": q, "j": j, "beta": beta,
        "adjacent_coefficients": {str(j-1): left, str(j): center, str(j+1): right},
        "log_concavity_difference": difference,
        "conjectured_alpha_lower_bound": required_alpha,
        "explicit_RS42_counterexample": failed_target,
        "statistics": statistics,
        "resources": {
            "wall_seconds": time.perf_counter() - start,
            "user_cpu_seconds": usage.ru_utime,
            "system_cpu_seconds": usage.ru_stime,
            "max_rss_KiB": usage.ru_maxrss,
            "address_space_limits_bytes": list(resource.getrlimit(resource.RLIMIT_AS)),
            "cpu_limits_seconds": list(resource.getrlimit(resource.RLIMIT_CPU)),
            "cpu_affinity": sorted(os.sched_getaffinity(0)),
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True), flush=True)
    if not failed_target:
        raise ValueError("fixed graph did not refute the explicit target")
    signal.alarm(0)


if __name__ == "__main__":
    main()
