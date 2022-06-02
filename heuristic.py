from collections import defaultdict
import itertools

import preprocessing
import tools
from tools import find_short_cycles, count_occurence
from functools import cmp_to_key

from vertex_cover import from_ordered_graph


def sat_turbocharge(g):
    from pysat.solvers import Cadical
    from pysat.card import CardEnc, EncType, ITotalizer
    from pysat.formula import IDPool, CNF

    budget = 100
    cycles = find_short_cycles(g)
    cnts = count_occurence(cycles)
    ordering = list(sorted(g.nodes, key=lambda x: cnts[x]))
    solution = set()
    positions = {x: i for (i, x) in enumerate(ordering)}

    for i, cn in enumerate(ordering):
        if any(positions[cn2] < i for cn2 in g._succ[cn]):
            solution.add(cn)

    ub = len(solution) - 1
    print(f"Starting bound {ub}")
    if tools.find_cycle(g, solution):
        print("ERROR, not a DFVS")

    while True:
        new_solution = set()
        for i, cn in enumerate(ordering):
            if any(positions[cn2] < i for cn2 in g._succ[cn]):
                new_solution.add(cn)

                # Point of regret, try reordering
                if len(new_solution) > ub:
                    start_idx = max(0, i - budget + 1)
                    target_nodes = set(ordering[start_idx: i+1])
                    delta = new_solution & target_nodes
                    new_solution -= delta
                    # preprocessing.preprocess_ignore(g, new_solution)
                    # If there is a successor ordered before, beyond the scope of this, then we have to have it in the dfvs
                    fixed = set()
                    for u in list(delta):
                        if any(positions[v] < start_idx for v in g._succ[u]):
                            fixed.add(u)

                    with Cadical() as csolv:
                        def _ord(x, y):
                            if x < y:
                                return pool.id(f"ord{x}_{y}")
                            else:
                                return -pool.id(f"ord{y}_{x}")

                        pool = IDPool()
                        limiter = []

                        for cn1 in target_nodes:
                            if cn1 in fixed:
                                csolv.add_clause([pool.id(f"{cn1}")])
                            else:
                                limiter.append(pool.id(f"{cn1}"))

                                for cn2 in g._succ[cn1]:
                                    if cn2 in target_nodes:
                                        csolv.add_clause([_ord(cn1, cn2), pool.id(f"{cn1}")])

                            for cn2 in target_nodes:
                                if cn2 != cn1:
                                    for cn3 in target_nodes:
                                        if cn1 != cn3 and cn2 != cn3:
                                            csolv.add_clause([-_ord(cn1, cn2), -_ord(cn2, cn3), _ord(cn1, cn3)])

                        csolv.append_formula(CardEnc.atmost(limiter, len(delta) - len(fixed) - 1, top_id=pool.top+1, encoding=EncType.totalizer))

                        if csolv.solve():
                            print("Improved")
                            model = csolv.get_model()
                            model = [x > 0 for x in model]
                            model.insert(0, None)

                            def compare(x1, x2):
                                if x1 == x2:
                                    return 0
                                elif model[_ord(x1, x2)]:
                                    return -1
                                else:
                                    return 1

                            for u in target_nodes:
                                if model[pool.id(f"{u}")]:
                                    new_solution.add(u)

                            ordered_targets = sorted(target_nodes, key=cmp_to_key(compare))
                            for idx, u in enumerate(ordered_targets):
                                positions[u] = start_idx + idx
                                ordering[start_idx + idx] = u
                        else:
                            print(f"Failed improvement at bound {ub}")
                            new_solution = None
                            break

        # TODO: Maybe fix some intermediate vertices...
        if new_solution:
            print(f"Improved to bound {ub}")
            if tools.find_cycle(g, new_solution):
                print("ERROR, not a DFVS")
            solution = new_solution
            ub -= 1
        else:
            budget += 50


def maxsat_ordering(g, start = None):
    import networkx as nx
    # cycles = find_short_cycles(g)
    # cnts = count_occurence(cycles)#list(sorted(g.nodes, key=lambda x: cnts[x]))
    if start is None:
        ordering = list(g.nodes) 
    else:
        ordering = start
    improved = True
    vc = from_ordered_graph(ordering, g)
    weight, solution = vc.solve_heuristic()
    print(weight, solution)
    ordering = list(nx.topological_sort(g.subgraph(set(g.nodes).difference(solution)))) + list(solution)
    last = weight
    while improved:
        vc = from_ordered_graph(ordering, g)
        weight, solution = vc.solve_heuristic()
        print(weight, solution)
        ordering = list(nx.topological_sort(g.subgraph(set(g.nodes).difference(solution)))) + list(solution)
        improved = weight < last
        last = weight
        
    def s_merge(order, sol):
        import random
        random.shuffle(sol)
        ret = []
        i1 = 0
        i2 = 0
        while i1 < len(order) and i2 < len(sol):
            if random.randint(0, len(order) - 1 + len(sol)) > len(order) - 1:
                ret.append(sol[i2])
                i2 += 1
            else:
                ret.append(order[i1])
                i1 += 1
        if i1 == len(order):
            ret += sol[i2:]
        else: 
            ret += order[i1:]
        return ret
    
    for _ in range(1000):
        ordering = s_merge(list(nx.topological_sort(g.subgraph(set(g.nodes).difference(solution)))), list(solution))
        vc = from_ordered_graph(ordering, g)
        weight, solution = vc.solve_heuristic()
        print(weight, solution)

    
    fvs = solution
    
    import random
    cur_best = fvs
    cur_min = len(fvs)
    for _ in range(1):
        random.shuffle(ordering)
        vc = from_ordered_graph(ordering, g)
        
        weight, solution = vc.solve_heuristic()
        
        fvs = solution
        if len(fvs) < cur_min:
            print("improved", len(fvs))
            cur_min = len(fvs)
            cur_best = fvs
    return cur_best

def select_sinkhorn(g):
    import networkx as nx
    import scipy.sparse as ssp
    import math
    from sklearn.utils.sparsefuncs import inplace_column_scale, inplace_row_scale
    adj = nx.adjacency_matrix(g)
    adj += ssp.diags([ 1 for _ in range(len(g.nodes)) ])
    for _ in range(math.ceil(math.log2(len(g.nodes)))):
        inplace_row_scale(adj, 1/ssp.linalg.norm(adj, axis= 1))
        #print(ssp.linalg.norm(adj, axis= 1))
        inplace_column_scale(adj, 1/ssp.linalg.norm(adj, axis= 0))
        #print(ssp.linalg.norm(adj, axis= 0))
    diag = adj.diagonal()
    v_and_pen = sorted(enumerate(diag), key= lambda x : -x[1])
    nodes = list(g.nodes)
    v_and_pen = [ (nodes[v],pen) for v,pen in v_and_pen ]
    return v_and_pen[0][0]

def sinkhorn(g):
    import networkx as nx
    fvs = []
    cur = g.copy()
    components = nx.strongly_connected_components(cur)
    q = [ g.subgraph(comp).copy() for comp in components if len(comp) > 1 ]
    while len(q) > 0:
        cur = q.pop()
        to_rem = select_sinkhorn(cur)
        cur.remove_node(to_rem)
        fvs.append(to_rem)
        components = nx.strongly_connected_components(cur)
        q += [ cur.subgraph(comp).copy() for comp in components if len(comp) > 1]
        
    fvs = reversed(fvs)
    final = set(fvs)
    for v in fvs:
        final.remove(v)
        if not nx.is_directed_acyclic_graph(g.subgraph(set(g.nodes).difference(final))):
            final.add(v)
    return final
    
    
def select_max_deg(g):
    outs = { v: len(g.out_edges(v)) for v in g.nodes }
    ins = { v: len(g.in_edges(v)) for v in g.nodes }
    worst = None
    score = -1 
    for v in g.nodes:
        if min(outs[v], ins[v]) > score:
            worst = v
            score = min(outs[v], ins[v])
    return worst

def max_deg(g):
    import networkx as nx
    fvs = []
    cur = g.copy()
    components = nx.strongly_connected_components(cur)
    q = [ g.subgraph(comp).copy() for comp in components if len(comp) > 1 ]
    while len(q) > 0:
        cur = q.pop()
        to_rem = select_max_deg(cur)
        cur.remove_node(to_rem)
        fvs.append(to_rem)
        components = nx.strongly_connected_components(cur)
        q += [ cur.subgraph(comp).copy() for comp in components if len(comp) > 1]
        
    fvs = reversed(fvs)
    final = set(fvs)
    for v in fvs:
        final.remove(v)
        if not nx.is_directed_acyclic_graph(g.subgraph(set(g.nodes).difference(final))):
            final.add(v)
    return final
    