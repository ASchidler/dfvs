import sys


def preprocess(g, verbose=False):
    # Preprocess
    selfloops = 0
    deg2 = 0
    deg0 = 0
    node_cnt = sys.maxsize

    included = []

    while len(g.nodes) < node_cnt:
        node_cnt = len(g.nodes)

        for cn in list(g.nodes):
            if cn in g._succ[cn]:
                selfloops += 1
                g.remove_node(cn)
                included.append(cn)
            elif len(g._succ[cn]) == 0 or len(g._pred[cn]) == 0:
                deg0 += 1
                g.remove_node(cn)
            elif len(g._succ[cn]) == 1:
                for cn2 in g._pred[cn]:
                    g.add_edge(cn2, next(iter(g._succ[cn])))
                deg2 += 1
                g.remove_node(cn)
            elif len(g._pred[cn]) == 1:
                for cn2 in g._succ[cn]:
                    g.add_edge(next(iter(g._pred[cn])), cn2)
                deg2 += 1
                g.remove_node(cn)
    if verbose:
        print(f"Preprocessing: {selfloops} Selfloops, {deg0} Degree 0, {deg2} Degree 2")
    return included

def preprocess_ignore(g, ignore):
    results = set()
    # Preprocess
    selfloops = 0
    deg2 = 0
    deg0 = 0
    node_cnt = sys.maxsize

    while len(g.nodes) < node_cnt:
        node_cnt = len(g.nodes)

        for cn in list(g.nodes):
            if cn in ignore:
                continue

            pred = [x for x in g._pred if x not in ignore]
            succ = [x for x in g._succ if x not in ignore]

            if cn in g._succ[cn]:
                selfloops += 1
                g.remove_node(cn)
                results.add(cn)
            elif len(succ) == 0 or len(pred) == 0:
                deg0 += 1
                results.add(cn)
            elif len(succ) == 1:
                deg2 += 1
                results.add(cn)
            elif len(pred) == 1:
                deg2 += 1
                results.add(cn)

    print(f"Ignore Preprocessing: {selfloops} Selfloops, {deg0} Degree 0, {deg2} Degree 2")