from collections import defaultdict


def find_cycle(g, ignore):
    """Finds a cycle in g, ignoring all vertices in ignore. E.g., if ignore is a DFVS candidate, this method returns None"""
    seen = set()
    while len(seen) < len(g.nodes) - len(ignore):
        pred = dict()
        start = next(iter(n for n in g.nodes if n not in ignore and n not in seen))
        visited = {start}
        stack = [start]

        while stack:
            cn = stack.pop()
            for cs in g._succ[cn]:
                if cs in ignore:
                    continue
                if cs in visited:
                    cycle = [cs]
                    while cn != cs:
                        cycle.append(cn)
                        if cn not in pred:
                            cycle = None  # Reached beginning, without finding node, not circle
                            break
                        cn = pred[cn]
                    if cycle is not None:
                        return cycle
                else:
                    pred[cs] = cn
                    stack.append(cs)
                    visited.add(cn)
        seen.update(visited)

    return None


def find_short_cycles(g, verbose=False):
    # Find small cycles
    cycles = []
    cycle_cnt = defaultdict(int)

    for cn in g.nodes:
        for cn2 in g._succ[cn]:
            if cn < cn2:
                if cn in g._succ[cn2]:
                    cycles.append([cn, cn2])
                    cycle_cnt[2] += 1
                else:
                    for cn3 in g._succ[cn2]:
                        if cn < cn3 and cn in g._succ[cn3]:
                            cycles.append([cn, cn2, cn3])
                            cycle_cnt[3] += 1

    if verbose:
        for c_l in sorted(cycle_cnt.keys()):
            print(f"{c_l}-Cycle Count: {cycle_cnt[c_l]}")

    disjoint = 0
    found = set()
    for cc in cycles:
        if not any(x in found for x in cc):
            disjoint += 1
            found.update(cc)

    if verbose:
        print(f"Approx. {disjoint} Disjoint")

    return cycles


def find_cycles_length(g, length):
    def find_sub_cycle(on, cn, d):
        if d == 0:
            return []
        c_result = []
        if d == 1:
            if on in g._succ[cn]:
                return [[cn]]
            return []
        for n2 in g._succ[cn]:
            if n2 == on:
                return []
            elif n2 > on:
                nc = find_sub_cycle(on, n2, d-1)
                for ncc in nc:
                    ncc.append(cn)
                c_result.extend(nc)
        return c_result

    cycles = []
    for n in g.nodes:
        cycles.extend(find_sub_cycle(n, n, length))

    print(f"{length}-Cycles: {len(cycles)}")
    return cycles


def count_occurence(sets, verbose=False):
    # Count vertex occurrence
    cnts = defaultdict(int)

    for cc in sets:
        for cn in cc:
            cnts[cn] += 1

    ones = 0
    for cv in cnts.values():
        if cv == 1:
            ones += 1

    if verbose:
        print(f"{ones} single occurences")

    return cnts