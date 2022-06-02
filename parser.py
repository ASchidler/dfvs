import networkx as nx


def parse(stream):
    g = nx.DiGraph()
    cnt = 0
    for cl in stream:
        if cl.strip().startswith("%"):
            continue
        if cnt > 0:
            for cn in cl.strip().split(" "):
                if cn != "":
                    g.add_edge(cnt, int(cn.strip()))
        cnt += 1

    return g
