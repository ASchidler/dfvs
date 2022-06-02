from random import randint
from sys import maxsize

import networkx as nx
from networkx import DiGraph


def ordering_to_decomp(g_in, ordering):
    """Converts an elimination ordering into a decomposition, returns bag, tree and the tree's root"""

    bags = {n: {n} for n in ordering}
    tree = DiGraph()
    ps = {x: ordering.index(x) for x in ordering}

    # Add edges to bags
    for u, v in g_in.edges:
        if ps[v] < ps[u]:
            u, v = v, u
        bags[u].add(v)

    for n in ordering:
        A = set(bags[n])
        if len(A) > 1:
            A.remove(n)
            _, nxt = min((ps[x], x) for x in A)

            bags[nxt].update(A)
            tree.add_edge(nxt, n)

    return bags, tree, ordering[len(ordering) - 1]


def clean_tree(bags, tree, root):
    """Cleans the tree by removing subsumed bags, i.e. the resulting decomposition will be equal but smaller"""
    import queue as qu
    # Remove subsumed bags
    q = qu.Queue()
    q.put(root)

    while not q.empty():
        n = q.get()

        nbs = set(tree.successors(n))
        nbs.update(tree.predecessors(n))
        target = None

        for u in nbs:
            if bags[u].issubset(bags[n]) or bags[u].issuperset(bags[n]):
                target = u
                break

        if target is None:
            for u in tree.successors(n):
                q.put(u)

        else:
            q.put(target)
            for u in tree.successors(n):
                if u != target:
                    tree.add_edge(target, u)
            for u in tree.predecessors(n):
                if u != target:
                    tree.add_edge(u, target)

            bags[target] = bags[target] if len(bags[target]) >= len(bags[n]) else bags[n]
            bags.pop(n)
            tree.remove_node(n)

    return tree, bags


def greedy(g, criterion):
    """Basic greedy heuristic that establishes an elimination ordering based on a given criterion"""
    ordering = []

    while len(ordering) != len(g.nodes):
        ordering.append(criterion.next())

    bound = max(len(x) for x in ordering_to_decomp(g, ordering)[0].values()) - 1
    #bound = improve_scramble(g, ordering, bound=bound)
    #bound = improve_swap(g, ordering, bound=bound)

    return bound, ordering


def improve_swap(g, ordering, rounds=500, bound=maxsize):
    """Tries to improve the bound of an elimination ordering by swapping random elements"""

    o = bound
    for _ in range(0, rounds):
        t1 = randint(0, len(ordering) - 1)
        t2 = randint(0, len(ordering) - 1)

        ordering[t1], ordering[t2] = ordering[t2], ordering[t1]

        result = max(len(x) for x in ordering_to_decomp(g, ordering)[0].values()) - 1

        if result > bound:
            ordering[t1], ordering[t2] = ordering[t2], ordering[t1]
        else:
            bound = result

    return bound


def improve_scramble(g, ordering, rounds=100, bound=maxsize, interval=15):
    """Tries to improve the bound by randomly scrambling the elements in an interval"""

    limit = len(ordering) - 1 - interval if len(ordering) > interval else 0
    interval = min(interval, len(ordering))

    for _ in range(0, rounds):
        index = randint(0, limit) if limit > 0 else 0

        old = ordering[index:index+interval]
        for c_i in range(0, interval-1):
            randindex = randint(0, interval - 1 - c_i) + index + c_i
            ordering[index + c_i], ordering[randindex] = ordering[randindex], ordering[index + c_i]

        result = max(len(x) for x in ordering_to_decomp(g, ordering)[0].values()) - 1

        # If the new bound is worse, restore
        if result > bound:
            for i in range(0, interval):
                ordering[index + i] = old[i]
        else:
            bound = result

    return bound


def greedy_min_degree(g_in):
    return greedy(g_in, MinDegreeCriterion(g_in))


class MinDegreeCriterion:
    """Always returns the vertex with lowest degree"""
    def __init__(self, g):
        self.g = g.copy()

        # q is a bucket queue
        self.max_degree = 0
        self.q = [set()]
        for k, v in ((n, len(g[n])) for n in g.nodes):
            if v > self.max_degree:
                for _ in range(0, v - self.max_degree):
                    self.q.append(set())
                self.max_degree = v

            self.q[v].add(k)

        self.cmin = 0

    def choose(self):
        # Choose min degree vertex
        return self.q[self.cmin].pop()

    def next(self):
        while len(self.q[self.cmin]) == 0:
            self.cmin += 1
            if self.cmin > self.max_degree:
                return None

        n = self.choose()

        # Eliminate
        nb = self.g[n]

        # First remove vertex
        self.g.remove_node(n)

        # Decrement degree of neighbors
        for u in nb:
            # Decrement, since degree will decrease after removing n
            self.update_degree(u, -1)

        # Introduce clique among neighbors
        for u, v in ((u, v) for u in nb for v in nb if u > v and u not in self.g[v]):
            self.g.add_edge(u, v)
            self.update_degree(u, 1)
            self.update_degree(v, 1)

        return n

    def update_degree(self, n, inc):
        dgn = len(self.g[n])
        dg = dgn - inc

        if dgn > self.max_degree:
            self.q.append(set())
            self.max_degree = dgn
        if dgn < self.cmin:
            self.cmin = dgn

        self.q[dg].remove(n)
        self.q[dgn].add(n)

