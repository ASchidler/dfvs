from collections import defaultdict
import itertools
from hitting_set import from_graph

import tools
from tools import find_short_cycles, count_occurence

def sat_hs(g, verbose=False):
    from pysat.solvers import Cadical
    from pysat.card import CardEnc, EncType, ITotalizer
    from pysat.formula import IDPool, CNF
    cycles = find_short_cycles(g, verbose=verbose)
    cnts = count_occurence(cycles, verbose=verbose)
    heur = set()

    for cc in cycles:
        if not any(x in heur for x in cc):
            _, selection = max((cnts[cn], cn) for cn in cc)
            heur.add(selection)

    if verbose:
        print(f"Heuristic Hitting Set: {len(heur)}")

    ub = len(heur) - 1
    sat = True
    last_model = None

    with Cadical() as csolv:
        pool = IDPool()
        for cc in cycles:
            csolv.add_clause([pool.id(f"{cn}") for cn in cc])

        with ITotalizer(pool.id2obj.keys(), ub, pool.top + 1) as itot:
            csolv.append_formula(itot.cnf)
            csolv.add_clause([-itot.rhs[ub]])

            while sat:
                sat = csolv.solve()
                if sat:
                    if verbose:
                        print(f"Success {ub}")
                    ub -= 1
                    last_model = csolv.get_model()
                    csolv.add_clause([-itot.rhs[ub]])
                else:
                    if verbose:
                        print(f"Failure {ub}")

    if last_model is None:
        fvs = heur
    else:
        fvs = []
        for c_val in last_model:
            if c_val > 0 and c_val in pool.id2obj:
                fvs.append(int(pool.obj(c_val)))

    found_cycle = True
    nsolv = None
    ub += 1
    changed = True
    while found_cycle or not changed:
        found_cycle = False
        fvs = set(fvs)
        added_cycle = True
        cnt = 0

        c_solution = set(fvs)
        while added_cycle and changed:
            added_cycle = False
            new_cycle = tools.find_cycle(g, c_solution)
            if new_cycle is not None:
                added_cycle = new_cycle
                found_cycle = found_cycle or added_cycle
                c_solution.update(new_cycle)
                cycles.append(new_cycle)
                if nsolv is not None:
                    nsolv.add_clause([pool.id(f"{cn}") for cn in new_cycle])

                cnt += 1

        if cnt > 0 or not changed:
            if verbose:
                print(f"Added {cnt} cycles")

            if nsolv is None:
                nsolv = Cadical()
                pool = IDPool()
                # for cn in g.nodes:
                #     pool.id(f"{cn}")

                for cc in cycles:
                    nsolv.add_clause([pool.id(f"{cn}") for cn in cc])
                nsolv.append_formula(CardEnc.atmost(pool.id2obj.keys(), ub, pool.top + 1))

            if nsolv.solve():
                changed = True
                found_cycle = True
                if verbose:
                    print(f"Success {ub}")
                fvs = set()
                last_model = nsolv.get_model()
                for c_val in last_model:
                    if c_val > 0 and c_val in pool.id2obj:
                        fvs.add(int(pool.obj(c_val)))
            else:
                changed = False
                nsolv.delete()
                nsolv = None
                ub += 1
                if verbose:
                    print(f"Failure {ub}")

    if nsolv is not None:
        nsolv.delete()

    return fvs


def maxsat_hs(g, verbose=False):
    hs = from_graph(g, verbose=verbose)
    weight, solution = hs.solve_maxsat()
    fvs = [ -c_val for c_val in solution if c_val < 0]

    found_cycle = True
    while tools.find_cycle(g, fvs):
        added_cycle = True
        cnt = 0

        c_solution = set(fvs)
        while added_cycle:
            added_cycle = False
            new_cycle = tools.find_cycle(g, c_solution)
            if new_cycle is not None:
                added_cycle = True
                c_solution.update(new_cycle)
                hs.sets.append(new_cycle)

                cnt += 1

        if found_cycle:
            if verbose:
                print(f"Added {cnt} cycles")
            weight, solution = hs.solve_maxsat()
            fvs = [ -c_val for c_val in solution if c_val < 0]

    return fvs

def sat_ordering(g):
    from pysat.solvers import Cadical
    from pysat.card import CardEnc, EncType, ITotalizer
    from pysat.formula import IDPool, CNF
    cycles = find_short_cycles(g)
    cnts = count_occurence(cycles)
    ordering = list(sorted(g.nodes, key=lambda x: cnts[x]))
    positions = {x: i for (i, x) in enumerate(ordering)}
    binaries = 0
    sat = True
    heur = set()
    last_model = None

    with Cadical() as csolv:
        pool = IDPool()
        cnt2 = defaultdict(int)
        for i, cn in enumerate(ordering):
            for cn2 in g._pred[cn]:
                if positions[cn2] < i:
                    csolv.add_clause([pool.id(f"{cn}"), pool.id(f"{cn2}")])
                    binaries += 1
                    cnt2[cn] += 1
                    cnt2[cn2] += 1
                    heur.add(cn)
        ones = sum(1 if v == 1 else 0 for v in cnt2.values())
        print(f"Binaries {binaries}, ones {ones}, UB: {len(heur)}")

        ub = len(heur) - 1
        with ITotalizer(pool.id2obj.keys(), ub, pool.top + 1) as itot:
            csolv.append_formula(itot.cnf)
            csolv.add_clause([-itot.rhs[ub]])

            while sat:
                sat = csolv.solve()
                if sat:
                    print(f"Success {ub}")
                    ub -= 1
                    last_model = csolv.get_model()
                    csolv.add_clause([-itot.rhs[ub]])
                else:
                    print(f"Failure {ub}")
    if last_model is None:
        return heur

    fvs = []
    for c_val in last_model:
        if c_val > 0 and c_val in pool.id2obj:
            fvs.append(int(pool.obj(c_val)))

    return fvs


def sat_full(g):
    from pysat.solvers import Cadical
    from pysat.card import CardEnc, EncType, ITotalizer
    from pysat.formula import IDPool, CNF
    cycles = find_short_cycles(g)
    cnts = count_occurence(cycles)
    ordering = list(sorted(g.nodes, key=lambda x: cnts[x]))
    positions = {x: i for (i, x) in enumerate(ordering)}
    heur = set()
    last_model = None
    for i, cn in enumerate(ordering):
        for cn2 in g._pred[cn]:
            if positions[cn2] < i:
                heur.add(cn)

    ub = len(heur)
    pool = IDPool()

    def _ord(x, y):
        if x < y:
            return pool.id(f"ord{x}_{y}")
        else:
            return -pool.id(f"ord{y}_{x}")

    with Cadical() as csolv:
        limiter = [pool.id(f"{x}") for x in g.nodes]

        for cn1 in g.nodes:
            for cn2 in g._succ[cn1]:
                csolv.add_clause([_ord(cn1, cn2), pool.id(f"{cn1}")])

            for cn2 in g.nodes:
                if cn2 != cn1:
                    for cn3 in g.nodes:
                        if cn1 != cn3 and cn2 != cn3:
                            csolv.add_clause([-_ord(cn1, cn2), -_ord(cn2, cn3), _ord(cn1, cn3)])

        with ITotalizer(limiter, ub, pool.top + 1) as itot:
            csolv.append_formula(itot.cnf)
            csolv.add_clause([-itot.rhs[ub]])

            sat = True
            while sat:
                sat = csolv.solve()
                if sat:
                    last_model = csolv.get_model()
                    ub -= 1
                    csolv.add_clause([-itot.rhs[ub]])
                    print(f"Success {ub}")
                else:
                    print(f"Failed {ub}")

    if last_model is None:
        return heur
    else:
        solution = set()
        for cv in last_model:
            if cv > 0:
                if cv not in pool.id2obj:
                    break
                cid = pool.obj(cv)
                try:
                    solution.add(int(cid))
                except ValueError:
                    return solution

    return solution



