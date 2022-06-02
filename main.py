from collections import defaultdict

import parser as p
import preprocessing as pp
import sys

import exact_methods as em
import tools
import heuristic
import matplotlib.pyplot as plt
import networkx as nx

verbose = True


def check_tw(g):
    import tw

    g_ud = g.to_undirected()
    bound, ordering = tw.greedy_min_degree(g_ud)
    print(f"TW: {bound}")
    bags, tree, root = tw.ordering_to_decomp(g_ud, ordering)
    tw.clean_tree(bags, tree, root)
    print(f"Tree Nodes: {len(tree.nodes)}")

    for u in tree.nodes:
        total = set()
        q = [u]
        while q:
            v = q.pop()
            total.update(bags[v])
            q.extend(tree.successors(v))
        bag_ins = set()
        bag_outs = set()
        for v in bags[u]:
            bag_ins.update(g._pred[v])
            bag_outs.update(g._succ[v])
        left_side = total - bags[u]
        right_side = set(g.nodes) - total
        left_in = len(bag_ins & left_side)
        left_out = len(bag_outs & left_side)
        right_in = len(bag_ins & right_side)
        right_out = len(bag_outs & right_side)
        if len(left_side) > 0 and len(right_side) > 0 or len(bags[u]) > 50:
            print(f"TWN\t{len(bags[u])}\t{len(left_side)}\t{len(right_side)}\t{left_in}/{left_out}\t{right_in}/{right_out}")


def check_scc(g):
    from networkx.algorithms.components import strongly_connected_components

    scc = list(strongly_connected_components(g))
    print(f"SCCs: {len(scc)}, Max: {max(len(x) for x in scc)}")
    

def main_method():
    if len(sys.argv) > 1 and len(sys.argv[1].strip()) > 0:
        with open(sys.argv[1]) as inp:
            g = p.parse(inp)
    else:
        g = p.parse(sys.stdin)

    pre_included = pp.preprocess(g, verbose=verbose)
    # plt.figure(num=None, figsize=(20, 20), dpi=80)
    # nx.draw(g, pos=nx.spectral_layout(g))
    # plt.show()
    # exit(0)

    # check_tw(g)
    if len(g.nodes) == 0:
        if verbose:
            print(f"Is a DFVS, Size {len(pre_included)}")
        else:
            for cn in pre_included:
                print(cn)
    else:
        if verbose:
            print(f"{len(g.nodes)} Nodes, {len(g.edges)} Edges")
        if verbose:
            gd = g.copy()
            cycles = tools.find_short_cycles(gd, True)
            for cc in cycles:
                if len(cc) == 2:
                    gd.remove_edge(cc[0], cc[1])
                    gd.remove_edge(cc[1], cc[0])
            check_scc(gd)

            gtwo = nx.Graph()
            for u, v in g.edges:
                if g.has_edge(v, u):
                    gtwo.add_edge(u, v)

            print(f"Two: {len(gtwo.nodes)}/ {len(gtwo.edges)}")
            found_any = True
            while found_any:
                for n in gtwo.nodes:
                    nbs = set(gtwo[n])
                    is_cq = True
                    for n2 in gtwo[n]:
                        if len(set(gtwo[n2]) & nbs) < len(nbs) - 1 or len(g[n2]) <= len(g[n]):
                            is_cq = False
                            break
                    if is_cq:
                        print("yay")
                # found_any = False
                # for cq in nx.find_cliques(gtwo):
                #     sq = set(cq)
                #     for n in sq:
                #         any_outside = False
                #         for n2 in g[n]:
                #             if n2 not in sq:
                #                 any_outside = True
                #                 break
                #         if not any_outside:
                #             g.remove_node(n)
                #             gtwo.remove_node(n)
                #             print("Found one")
                #             # found_any = True
                #             # break
            pp.preprocess(g)
                    #print(f"Clique: {len(cq)}")

            # check_tw(gd)
        if verbose:
            print(f"{len(g.nodes)} Nodes, {len(g.edges)} Edges")
        # heuristic.sat_turbocharge(g)

        # solution = em.sat_full(g)
        # if not tools.find_cycle(g, set(solution)) is None:
        #     print("Not a DFVS")
        # else:
        #     print(f"Is a DFVS, Size {len(solution)}")
        # print("\n\n\n")

        solution = em.maxsat_hs(g, verbose=verbose)
        #solution = em.sat_hs(g, verbose=verbose)

        if verbose:
            if not tools.find_cycle(g, set(solution)) is None:
                print("Not a DFVS")
            else:
                print(f"Is a DFVS, Size {len(solution)}")
            print("\n\n\n")
        else:
            for cn in pre_included:
                print(cn)
            for cn in solution:
                print(cn)

        # solution = em.sat_ordering(g)
        # if not tools.find_cycle(g, set(solution)) is None:
        #     print("Not a DFVS")
        # else:
        #     print(f"Is a DFVS, Size {len(solution)}")
        # print("\n\n\n")
        
        # solution = heuristic.sinkhorn(g)
        
        # #solution = heuristic.maxsat_ordering(g)
        # if verbose:
        #     import networkx as nx
        #     test = g.subgraph(set(g.nodes).difference(solution)).copy()
        #     if not nx.is_directed_acyclic_graph(test):
        #         print("Not a DFVS")
        #     else:
        #         print(f"Is a DFVS, Size {len(solution)}")
        #     print("\n\n\n")
        # else:
        #     for cn in pre_included:
        #         print(cn)
        #     for cn in solution:
        #         print(cn)
        
        # solution = heuristic.max_deg(g)
        # if verbose:
        #     import networkx as nx
        #     test = g.subgraph(set(g.nodes).difference(solution)).copy()
        #     if not nx.is_directed_acyclic_graph(test):
        #         print("Not a DFVS")
        #     else:
        #         print(f"Is a DFVS, Size {len(solution)}")
        #     print("\n\n\n")
        # else:
        #     for cn in pre_included:
        #         print(cn)
        #     for cn in solution:
        #         print(cn)
        # from vertex_cover import from_ordered_graph
        # vc = from_ordered_graph(list(nx.topological_sort(test)), test)
        # solution = heuristic.maxsat_ordering(g, start = list(nx.topological_sort(test)) + list(solution))
        # if verbose:
        #     import networkx as nx
        #     test = g.subgraph(set(g.nodes).difference(solution)).copy()
        #     if not nx.is_directed_acyclic_graph(test):
        #         print("Not a DFVS")
        #     else:
        #         print(f"Is a DFVS, Size {len(solution)}")
        #     print("\n\n\n")
        # else:
        #     for cn in pre_included:
        #         print(cn)
        #     for cn in solution:
        #         print(cn)


if __name__ == '__main__':
    main_method()
