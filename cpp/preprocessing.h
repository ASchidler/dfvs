//
// Created by aschidler on 5/10/22.
//

#ifndef CPP_PREPROCESSING_H
#define CPP_PREPROCESSING_H


#include "../external/EvalMaxSAT/lib/glucose/src/glucose/core/Solver.h"
#include "graph.h"
#include <queue>
#include <iostream>
#include <limits.h>
#include <string.h>
#include <map>
#include "dfvs.h"

namespace dfvs {

    bool still_consistent(vector<node_t>& node_to_scc, vector<vector<node_t>> sccs, node_t n) {
        return find(sccs[node_to_scc[n]].begin(), sccs[node_to_scc[n]].end(), n) != sccs[node_to_scc[n]].end();
    }
    bool is_diclique(Graph& g, const unordered_set<node_t>& nodes) {
        for(auto n1 : nodes) {
            const unordered_set<node_t>& outs = g.get_succ(n1);
            for(auto n2 : nodes) {
                if(n1 != n2 && outs.find(n2) == outs.end()) {
                    return false;
                }
            }
        }
        return true;
    }
    bool check_indiclique(Graph& g, node_t n) {
        return is_diclique(g, g.get_pred(n));
    }

    bool check_outdiclique(Graph& g, node_t n) {
        return is_diclique(g, g.get_succ(n));
    }

    bool check_bipartite(Graph& g, unordered_map<node_t, int>& colorArr, node_t src, unordered_set<node_t> nodes, node_t& colored) {
        // Code from https://www.geeksforgeeks.org/bipartite-graph/
        // Create a color array to store colors
        // assigned to all vertices. Vertex
        // number is used as index in this array.
        // The value '-1' of colorArr[i]
        // is used to indicate that no color
        // is assigned to vertex 'i'. The value 1
        // is used to indicate first color
        // is assigned and value 0 indicates
        // second color is assigned.
        // Assign first color to source
        colorArr[src] = 1;
        // keep track of the colored vertices
        colored++;

        // Create a queue (FIFO) of vertex
        // numbers and enqueue source vertex
        // for BFS traversal
        queue <node_t> q;
        q.push(src);

        // Run while there are vertices
        // in queue (Similar to BFS)
        while (!q.empty())
        {
            // Dequeue a vertex from queue ( Refer http://goo.gl/35oz8 )
            node_t u = q.front();
            q.pop();

            // Return false if there is a self-loop
            //if (G[u][u] == 1)
            //return false;

            // Find all non-colored adjacent vertices
            for (auto v : nodes)
            {
                // An edge from u to v exists and
                // destination v is not colored
                if (v != u && (g.get_pred(u).find(v) == g.get_pred(u).end() || g.get_succ(u).find(v) == g.get_succ(u).end())) {
                    // there is an edge because there isnt one in the original graph
                    if(colorArr[v] == -1){
                        // Assign alternate color to this adjacent v of u
                        colorArr[v] = 1 - colorArr[u];
                        colored += colorArr[v];
                        q.push(v);
                    } else if(colorArr[v] == colorArr[u]) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    bool check_diclique2(Graph& g, node_t n) {
        unordered_set<node_t> both;
        const unordered_set<node_t> pred = g.get_pred(n);
        const unordered_set<node_t> succ = g.get_succ(n);
        // iterate over all nodes that are both successors and predecessors
        for(auto n1 : succ) {
            if(pred.find(n1) != pred.end()) {
                // check if the addition of n1 to both is still a diclique
                for(auto n2 : both) {
                    if(g.get_succ(n2).find(n1) == g.get_succ(n2).end() || g.get_pred(n2).find(n1) == g.get_pred(n2).end()) {
                        return false;
                    }
                }
                both.insert(n1);
            }
        }

        if(both.size() == 0) {
            return false;
        }
        // both contains all vertices that are both successors and predecessor
        // both is a diqlique if we get here

        // now check if we can partition the neighbours of n into two disjoint dicliques
        // this can be done by check bipartiteness of the undirected version of the complement graph 




        unordered_set<node_t> either(pred);
        either.insert(succ.begin(), succ.end());
        unordered_map<node_t, int> colorArr;
        node_t colored = 0;
        for (auto v : either) {
            colorArr[v] = -1;
        }

        // this is needed because there might be different connected components
        // first color all the both nodes though
        for (auto v : both) {
            if(colorArr[v] == -1) {
                if(!check_bipartite(g, colorArr, v, either, colored)) {
                    return false;
                }
            }
        }
        // only then color the remaining either nodes
        for(auto v : either) {
            // nodes that we have not found should always be colored
            if(colorArr[v] == -1) {
                assert(both.find(v) == both.end());
                if(!check_bipartite(g, colorArr, v, either, colored)) {
                    return false;
                }
            }
        }



        // If we reach here, then all adjacent
        // vertices can be colored with alternate color

        // we still need to check whether the vertices in both have the same color
        // and whether the diclique that contains the both set strictly contains the both set
        // we need every node in both to be colored and at least one more
        if(colored <= both.size()) {
            return false;
        }
        for(auto v : both) {
            if(colorArr[v] != 1) {
                return false;
            }
        }
        unordered_set<node_t> c0, c1;
        for(auto v : either) {
            assert(colorArr[v] != -1);
            if(colorArr[v] == 0) {
                c0.insert(v);
            } else {
                c1.insert(v);
            }
        }
        assert(is_diclique(g,c0));
        assert(is_diclique(g,c1));
        return true;
    }

    bool check_diclique3(Graph& g, node_t n) {
        unordered_set<node_t> either = g.get_pred(n);
        const unordered_set<node_t> succ = g.get_succ(n);
        // check if there is an overlap between the predecessors and successors
        // in this case, we cannot apply this reduction
        for(auto v : succ) {
            if(either.find(v) != either.end()) {
                return false;
            }
            either.insert(v);
        }
        // no shared vertices -> check for partition into three dicliques

        vector<Glucose::Solver *> dummy;
        Glucose::Solver solver(dummy);
        unordered_map<node_t, node_t> node_to_idx;
        node_to_idx.reserve(either.size());
        node_t i = 0;
        for(auto v : either) {
            solver.newVar();
            solver.newVar();
            solver.newVar();
            node_to_idx.insert(make_pair(v, i));
            i++;
        }
        i = 0;
        for(auto v : either) {
            for(auto w : either) {
                if(w != v && (g.get_succ(v).find(w) == g.get_succ(v).end() || g.get_pred(v).find(w) == g.get_pred(v).end())) {
                    // there is an edge between v and w in the complement
                    node_t j = node_to_idx[w];
                    solver.addClause(Glucose::mkLit(3*i, true), Glucose::mkLit(3*j, true));
                    solver.addClause(Glucose::mkLit(3*i + 1, true), Glucose::mkLit(3*j + 1, true));
                    solver.addClause(Glucose::mkLit(3*i + 2, true), Glucose::mkLit(3*j + 2, true));
                }
            }
            solver.addClause(Glucose::mkLit(3*i),Glucose::mkLit(3*i + 1),Glucose::mkLit(3*i + 2));
            i++;
        }
        return solver.solve();
    }

    bool check_dominated(Graph& g, node_t from, node_t to) {
        if(g.get_pred(from).find(to) != g.get_pred(from).end()) {
            return false;
        }
        const unordered_set<node_t> pred_f = g.get_pred(from);
        const unordered_set<node_t> succ_f = g.get_succ(from);
        const unordered_set<node_t> pred_t = g.get_pred(to);
        const unordered_set<node_t> succ_t = g.get_succ(to);
        bool dom = true;
        // check if all non-bidirectional predecessors of `from` are also predecessors of `to`
        for(auto v : pred_f) {
            if(succ_f.find(v) == succ_f.end() && pred_t.find(v) == pred_t.end()) { //
                dom = false;
                break;
            }
        }
        if(dom) {
            return true;
        }
        // check if all non-bidirectional successors of `from` are also successors of `to`
        for(auto v : succ_t) {
            if(pred_t.find(v) == pred_t.end() && succ_f.find(v) == succ_f.end()) { //
                return false;
            }
        }
        return true;
    }

    bool deep_check_dominated(Graph& g, node_t from, node_t to) {
        if(g.get_pred(from).find(to) != g.get_pred(from).end()) {
            return false;
        }
        const unordered_set<node_t> succ_f = g.get_succ(from);
        const unordered_set<node_t> pred_t = g.get_pred(to);
        bool dom = true;
        // check if there is a path from `from` to `to` using only single directional backward edges
        // that does not use any of the predecessors of `to`
        unordered_set<node_t> visited(pred_t.begin(), pred_t.end());
        visited.insert(from);
        vector<node_t> stack;
        stack.push_back(from);
        while(!stack.empty()) {
            node_t cur = stack.back();
            stack.pop_back();
            for(auto v : g.get_pred(cur)) {
                if(g.get_succ(cur).find(v) != g.get_succ(cur).end()) {
                    continue;
                }
                if(v == to) {
                    dom = false;
                    break;
                }
                if(visited.find(v) == visited.end()) {
                    stack.push_back(v);
                    visited.insert(v);
                }
            }
            if(!dom) {
                break;
            }
        }
        if(dom) {
            return true;
        }
        // check if there is a path from `to` to `from` using only single directional forward edges
        // that does not use any of the successors of `from`
        visited.clear();
        visited.insert(succ_f.begin(), succ_f.end());
        visited.insert(to);
        stack.clear();
        stack.push_back(to);
        while(!stack.empty()) {
            node_t cur = stack.back();
            stack.pop_back();
            for(auto v : g.get_succ(cur)) {
                if(g.get_pred(cur).find(v) != g.get_pred(cur).end()) {
                    continue;
                }
                if(v == to) {
                    return false;
                }
                if(visited.find(v) == visited.end()) {
                    stack.push_back(v);
                    visited.insert(v);
                }
            }
        }
        return true;
    }
    bool check_vc_subset(Graph& g, node_t n) {
        for(auto v : g.get_succ(n)) {
            if(g.get_succ(v).find(n) != g.get_succ(v).end()) {
                // candidate v
                // check if neighbors of v are all bidirectionally connected
                const unordered_set<node_t> succ = g.get_succ(v);
                const unordered_set<node_t> pred = g.get_pred(v);
                // if(succ.size() != pred.size()) {
                //     continue;
                // }
                // bool ok = true;
                // for(auto w : succ) {
                //     if(pred.find(w) == pred.end()) {
                //         ok = false;
                //         break;
                //     }
                // }
                // if(!ok) {
                //     continue;
                // }
                // all neighbors of v a re bidirectionally connected

                // check if every successor (except n) of v is also a successor of n
                bool ok = true;
                const unordered_set<node_t> succ_n = g.get_succ(n);
                const unordered_set<node_t> pred_n = g.get_pred(n);
                for(auto w : succ) {
                    if(w != n && succ_n.find(w) == succ_n.end()) {
                        ok = false;
                        break;
                    }
                }
                if(!ok) {
                    continue;
                }
                // check if every predecessor (except n) of v is also a predecessor of n 
                for(auto w : pred) {
                    if(w != n && pred_n.find(w) == pred_n.end()) {
                        ok = false;
                        break;
                    }
                }
                if(ok) {
                    return true;
                }
            }
        }
        return false;
    }

    bool check_vc_degree_one(Graph& g, node_t n) {
        return g.get_succ(n).size() == 1 && g.get_pred(n).size() == 1 && *g.get_succ(n).begin() == *g.get_pred(n).begin();
    }

    bool check_equal(Graph& g, node_t v, node_t w) {
        const unordered_set<node_t> succ_v = g.get_succ(v);
        const unordered_set<node_t> pred_v = g.get_pred(v);
        const unordered_set<node_t> succ_w = g.get_succ(w);
        const unordered_set<node_t> pred_w = g.get_pred(w);
        if(succ_v.find(w) == succ_v.end() && pred_v.find(w) == pred_v.end()) {
            if(succ_v.size() != succ_w.size() || pred_v.size() != pred_w.size()) {
                return false;
            }
            for(auto n : succ_v) {
                if(succ_w.find(n) == succ_w.end())  {
                    return false;
                }
            }
            for(auto n : pred_v) {
                if(pred_w.find(n) == pred_w.end())  {
                    return false;
                }
            }
        } else if(succ_v.find(w) != succ_v.end() && pred_v.find(w) == pred_v.end()) {
            if(succ_v.size() + 1 != succ_w.size() || pred_v.size() != pred_w.size()) {
                return false;
            }
            for(auto n : succ_v) {
                if(n != w && succ_w.find(n) == succ_w.end())  {
                    return false;
                }
            }
            for(auto n : pred_v) {
                if(pred_w.find(n) == pred_w.end())  {
                    return false;
                }
            }
        } else if(succ_v.find(w) == succ_v.end() && pred_v.find(w) != pred_v.end()) {
            if(succ_v.size() != succ_w.size() || pred_v.size() + 1 != pred_w.size()) {
                return false;
            }
            for(auto n : succ_v) {
                if(succ_w.find(n) == succ_w.end())  {
                    return false;
                }
            }
            for(auto n : pred_v) {
                if(n != w && pred_w.find(n) == pred_w.end())  {
                    return false;
                }
            }
        } else {
            return false;
        }
        return true;
    }

    bool check_subset(Graph& g, node_t v, node_t w) {
        // check if the successors of w are a subset of the successors of v
        // AND if the predecessors of w are a subset of the predecessors of v
        const unordered_set<node_t> succ_v = g.get_succ(v);
        const unordered_set<node_t> pred_v = g.get_pred(v);
        const unordered_set<node_t> succ_w = g.get_succ(w);
        const unordered_set<node_t> pred_w = g.get_pred(w);
        if(succ_v.size() < succ_w.size() || pred_v.size() < pred_w.size()) {
            return false;
        }
        for(auto n : succ_w) {
            if(succ_v.find(n) == succ_v.end())  {
                return false;
            }
        }
        for(auto n : pred_w) {
            if(pred_v.find(n) == pred_v.end())  {
                return false;
            }
        }
        return true;
    }

    bool check_double(Graph& g, node_t n, vector<node_t>& node_to_scc) {
        if(g.get_succ(n).size() != 2 || g.get_pred(n).size() != 2) {
            return false;
        }
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        // n has two edges which are in both directions
        node_t first = *g.get_succ(n).begin();
        node_t second = *(++g.get_succ(n).begin());
        return node_to_scc[first] != node_to_scc[second];
    }

    bool check_rule_6(Graph& g, node_t n, vector<node_t>& node_to_scc) {
        // n must have exactly three neighbors...
        if(g.get_succ(n).size() != 3 || g.get_pred(n).size() != 3) {
            return false;
        }
        // ...and they must be connected bidirectionally ...
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        auto it = g.get_succ(n).begin();
        node_t first = *it;
        node_t second = *(++it);
        node_t third = *(++it);
        // ...and there must not be any edges between them 
        // no edges between first and second
        if(g.get_succ(first).find(second) != g.get_succ(first).end() || g.get_pred(first).find(second) != g.get_pred(first).end()) {
            return false;
        }
        // no edges between first and third
        if(g.get_succ(first).find(third) != g.get_succ(first).end() || g.get_pred(first).find(third) != g.get_pred(first).end()) {
            return false;
        }
        // no edges between second and third
        if(g.get_succ(second).find(third) != g.get_succ(first).end() || g.get_pred(second).find(third) != g.get_pred(second).end()) {
            return false;
        }
        for(auto w : g.get_succ(n)) {
            for(auto v : g.get_succ(w)) {
                if(g.get_pred(w).find(v) == g.get_pred(w).end()) {
                    return false;
                }
            }
            for(auto v : g.get_pred(w)) {
                if(g.get_succ(w).find(v) == g.get_succ(w).end()) {
                    return false;
                }
            }
        }
        return true;
    }

    bool check_rule_72(Graph& g, node_t n, vector<node_t>& node_to_scc, node_t* nodes) {
        // n must have exactly four neighbors...
        if(g.get_succ(n).size() != 4 || g.get_pred(n).size() != 4) {
            return false;
        }
        // ...and they must be connected bidirectionally ...
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        auto it = g.get_succ(n).begin();
        nodes[0] = *it;
        nodes[1] = *(++it);
        nodes[2] = *(++it);
        nodes[3] = *(++it);
        node_t edges[] = {0,0,0,0};
        node_t total_edges = 0;
        for(node_t i = 0; i < 4; i++) {
            for(auto v : g.get_succ(nodes[i])) {
                for(node_t j = 0; j < 4; j++) {
                    // we do not need to check if i == j because nodes[i] cannot be a successor of itself
                    if(v == nodes[j]) {
                        if(g.get_pred(nodes[i]).find(nodes[j]) == g.get_pred(nodes[i]).end()) {
                            // we need bidirectional edges if any
                            return false;
                        }
                        if(i < j) {
                            // increase the edge counter
                            edges[i]++;
                            edges[j]++;
                            total_edges++;
                        }
                    }

                }
            }
            if(total_edges > 3) {
                return false;
            }
        }
        if(total_edges != 3) {
            return false;
        }
        node_t sorting[] = {0,1,2,3};
        // sort ascendingly by edges[i]
        sort(sorting, sorting + 4,
             [edges](const node_t & a, const node_t & b)
             {
                 return edges[a] < edges[b];
             });
        if(edges[sorting[0]] > 0) {
            return false;
        }
        // the next two loops make sure that the nodes are sorted by the number of edges they are in
        for (node_t i = 0; i < 4; i++) {
            sorting[i] = nodes[sorting[i]];
        }
        for (node_t i = 0; i < 4; i++) {
            nodes[i] = sorting[i];
        }
        return node_to_scc[nodes[0]] != node_to_scc[nodes[1]] && node_to_scc[nodes[0]] != node_to_scc[nodes[2]] && node_to_scc[nodes[0]] != node_to_scc[nodes[3]];
    }

    bool apply_rule_71(Graph& g, node_t n, vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc, vector<binary_reduced>& reconstruct) {
        // n must have exactly four neighbors...
        if(g.get_succ(n).size() != 4 || g.get_pred(n).size() != 4) {
            return false;
        }
        // ...and they must be connected bidirectionally ...
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        auto it = g.get_succ(n).begin();
        node_t nodes[4];
        nodes[0] = *it;
        nodes[1] = *(++it);
        nodes[2] = *(++it);
        nodes[3] = *(++it);
        node_t edges[] = {0,0,0,0};
        node_t total_edges = 0;
        for(node_t i = 0; i < 4; i++) {
            for(auto v : g.get_succ(nodes[i])) {
                for(node_t j = 0; j < 4; j++) {
                    // we do not need to check if i == j because nodes[i] cannot be a successor of itself
                    if(v == nodes[j]) {
                        if(g.get_pred(nodes[i]).find(nodes[j]) == g.get_pred(nodes[i]).end()) {
                            // we need bidirectional edges if any
                            return false;
                        }
                        if(i < j) {
                            // increase the edge counter
                            edges[i]++;
                            edges[j]++;
                            total_edges++;
                        }
                    }

                }
            }
            if(total_edges > 3) {
                return false;
            }
        }
        if(total_edges != 3) {
            return false;
        }

        // bring the nodes into the right order
        if (edges[0] != 1) {
            if (edges[1] == 1) {
                swap(nodes[0], nodes[1]);
                swap(edges[0], edges[1]);
            } else {
                swap(nodes[0], nodes[2]);
                swap(edges[0], edges[2]);
            }
        }

        if (edges[3] != 1) {
            if (edges[1] == 1) {
                swap(nodes[3], nodes[1]);
                swap(edges[3], edges[1]);
            } else {
                swap(nodes[3], nodes[2]);
                swap(edges[3], edges[2]);
            }
        }

        if (g.get_succ(nodes[0]).find(nodes[1]) == g.get_succ(nodes[0]).end()) {
            swap(nodes[1], nodes[2]);
            swap(edges[1], edges[2]);
        }

        node_t a = nodes[0];
        node_t b = nodes[1];
        node_t c = nodes[2];
        node_t d = nodes[3];
        if(edges[0] != 1 || edges[1] != 2 || edges[2] != 2 || edges[3] != 1) {
            return false;
        }
        assert(g.get_succ(nodes[0]).find(nodes[1]) != g.get_succ(nodes[0]).end());
        assert(g.get_succ(nodes[1]).find(nodes[2]) != g.get_succ(nodes[1]).end());
        assert(g.get_succ(nodes[2]).find(nodes[3]) != g.get_succ(nodes[2]).end());

        if(node_to_scc[a] == node_to_scc[b]
           || node_to_scc[a] == node_to_scc[c]
           || node_to_scc[a] == node_to_scc[d]
           || node_to_scc[b] == node_to_scc[d]) {
            return false;
        }


        vector<node_t> store_succ(g.get_succ(a).begin(), g.get_succ(a).end());
        vector<node_t> store_pred(g.get_pred(a).begin(), g.get_pred(a).end());


        // transfer edges from b to a
        for(auto v : g.get_succ(b)) {
            if(v != a) {
                g.add_edge(a, v);
            }
        }
        for(auto v : g.get_pred(b)) {
            if(v != a) {
                g.add_edge(v, a);
            }
        }
        // transfer edges from d to a
        for(auto v : g.get_succ(d)) {
            assert(v != a);
            g.add_edge(a, v);
        }
        for(auto v : g.get_pred(d)) {
            assert(v != a);
            g.add_edge(v, a);
        }
        // transfer edges from d to b
        for(auto v : g.get_succ(d)) {
            assert(v != b);
            g.add_edge(b, v);
        }
        for(auto v : g.get_pred(d)) {
            assert(v != b);
            g.add_edge(v, b);
        }

        for(auto n2: store_succ) {
            if (n2 != c)
                g.add_edge(c, n2);
            if (n2 != d)
                g.add_edge(d, n2);
        }
        for(auto n2: store_pred) {
            if (n2 != c)
                g.add_edge(n2, c);
            if (n2 != d)
                g.add_edge(n2, d);
        }

        // Make a,b,c,d a clique, i.e. 3 out of 4 will be in the VC
        g.add_edge(a, d);
        g.add_edge(d, a);
        g.add_edge(a, c);
        g.add_edge(c, a);
        g.add_edge(b, d);
        g.add_edge(d, b);

        //assert(vc.adjacent(a, b) && vc.adjacent(a, c) && vc.adjacent(a, d) && vc.adjacent(b, c) && vc.adjacent(b, d) && vc.adjacent(c, d));

        reconstruct.push_back({n, a, b, c, d, true, false});
        g.remove(n);
        // update the node to scc mapping
        // may be an overapproximation, i.e., if x,y are in the same scc according to this they still might not be
        // but this way of overapproximating only makes it so that we do not know that we can apply a rule even though we could
        // but not the other way around, which would be problematic

        // TODO: if the sccs are size one we can get a better approximation
        // we just take the union of all the sccs
        vector<node_t> new_scc;
        for(node_t i = 0; i < 4; i++) {
            for(auto v : sccs[node_to_scc[nodes[i]]]) {
                new_scc.push_back(v);
                node_to_scc[v] = node_to_scc[nodes[0]];
            }
        }
        sccs[node_to_scc[nodes[0]]] = new_scc;
        return true;
    }

    bool apply_rule_4_or_5(Graph& g, node_t n,  vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc, vector<binary_reduced>& reconstruct) {
        node_t degree = g.get_succ(n).size();
        if(degree != g.get_pred(n).size() || degree < 2) {
            return false;
        }
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        node_t twice = INVALID_NODE;
        vector<pair<node_t, node_t>> edges;
        edges.reserve(degree * (degree - 2) / 2);

        for (auto n2: g.get_succ(n)) {
            if ((g.get_succ(n2).size() == 1 && g.get_pred(n2).size() == 1)) {
                return false;
            }
            node_t cnb = 0;
            for (auto n3: g.get_succ(n)) {
                if (g.get_succ(n2).find(n3) != g.get_succ(n2).end()) {
                    // we need bidirectional edges
                    if(g.get_pred(n2).find(n3) == g.get_pred(n2).end()) {
                        return false;
                    }
                    cnb++;
                } else if (n2 < n3) {
                    edges.emplace_back(n2, n3);
                }
            }
            if (cnb == degree - 1) {
                return false;
            } else if (cnb == degree - 3) {
                twice = n2;
            }
        }

        if ((degree + 1)/ 2 != edges.size()) {
            return false;
        }

        for(auto& cedge : edges) {
            if(node_to_scc[cedge.first] == node_to_scc[cedge.second]) {
                return false;
            }
        }
        if (degree % 2 == 1) {
            assert(twice != INVALID_NODE);
            // first check that the nodes that connect to twice are in different SCCs
            // node_t first = INVALID_NODE;
            // for(auto& cedge : edges) {
            //     if(cedge.first == twice) {
            //         if(first == INVALID_NODE) {
            //             first = node_to_scc[cedge.second];
            //         } else if(node_to_scc[cedge.second] == first) {
            //             return false;
            //         }
            //     }
            // }
            for (auto &cedge: edges) {
                if(cedge.second == twice) {
                    swap(cedge.first, cedge.second);
                }
                if (cedge.first == twice) {
                    for(auto v : g.get_succ(twice)) {
                        assert(v != cedge.second);
                        g.add_edge(cedge.second, v);
                    }
                    for(auto v : g.get_pred(twice)) {
                        assert(v != cedge.second);
                        g.add_edge(v, cedge.second);
                    }
                }
            }
            g.remove(twice);
        }
        g.remove(n);

        vector<node_t> new_scc;
        for(auto& cedge : edges) {
            if (cedge.first != twice) {
                for(auto v : g.get_succ(cedge.first)) {
                    assert(v != cedge.second);
                    g.add_edge(cedge.second, v);
                }
                for(auto v : g.get_pred(cedge.first)) {
                    assert(v != cedge.second);
                    g.add_edge(v, cedge.second);
                }
                g.remove(cedge.first);
            }

            for(auto v : sccs[node_to_scc[cedge.first]]) {
                new_scc.push_back(v);
                node_to_scc[v] = node_to_scc[n];
            }
            for(auto v : sccs[node_to_scc[cedge.second]]) {
                new_scc.push_back(v);
                node_to_scc[v] = node_to_scc[n];
            }
        }
        sccs[node_to_scc[n]] = new_scc;
        reconstruct.push_back({n, twice, INVALID_NODE, INVALID_NODE, INVALID_NODE, false, false, false, move(edges)});
        return true;
    }

    bool apply_rule_8(Graph& g, node_t n,  vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc, vector<binary_reduced>& reconstruct) {
        // all edges of n must be bidirectional
        node_t degree = g.get_succ(n).size();
        if(degree != g.get_pred(n).size() || degree < 2) {
            return false;
        }
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        // get the edges of the cograph restricted to the neighbors of n
        unordered_map<node_t, vector<node_t>> edges;

        for (auto n2: g.get_succ(n)) {
            edges[n2] = vector<node_t>();
            if ((g.get_succ(n2).size() == 1 && g.get_pred(n2).size() == 1)) {
                return false;
            }
            node_t cnb = 0;
            for (auto n3: g.get_succ(n)) {
                if (g.get_succ(n2).find(n3) != g.get_succ(n2).end() && g.get_pred(n2).find(n3) != g.get_pred(n2).end()) {
                    cnb++;
                } else if(n3 != n2) {
                    // check feasibility with SCCs
                    if(node_to_scc[n2] == node_to_scc[n3]) {
                        // maybe we can still do something:
                        // check if the only non-bidirectional outgoing edge of n2 goes to n3
                        bool ok1 = true, ok2 = true, ok3 = true, ok4 = true;
                        for(auto out : g.get_succ(n2)) {
                            if(out != n3 && g.get_pred(n2).find(out) == g.get_pred(n2).end()) {
                                ok1 = false;
                                break;
                            }
                        }
                        // check if the only non-bidirectional outgoing edge of n3 goes to n2
                        for(auto out : g.get_succ(n3)) {
                            if(out != n2 && g.get_pred(n3).find(out) == g.get_pred(n3).end()) {
                                ok2 = false;
                                break;
                            }
                        }
                        // check if the only non-bidirectional incoming edge of n2 comes from n3
                        for(auto out : g.get_pred(n2)) {
                            if(out != n3 && g.get_succ(n2).find(out) == g.get_succ(n2).end()) {
                                ok3 = false;
                                break;
                            }
                        }
                        // check if the only non-bidirectional incoming edge of n3 comes from n2
                        for(auto out : g.get_pred(n3)) {
                            if(out != n2 && g.get_succ(n3).find(out) == g.get_succ(n3).end()) {
                                ok4 = false;
                                break;
                            }
                        }
                        if(g.get_succ(n3).find(n2) != g.get_succ(n3).end()) {
                            if(ok2 || ok3) {
                                edges[n2].push_back(n3);
                                continue;
                            }
                        } else if(g.get_succ(n2).find(n3) != g.get_succ(n2).end()) {
                            if(ok1 || ok4) {
                                edges[n2].push_back(n3);
                                continue;
                            }
                        }
                        // if((ok1 || ok4) && (ok2 || ok3)) {
                        //     edges[n2].push_back(n3);
                        //     continue;
                        // }
                        return false;
                    } else {
                        edges[n2].push_back(n3);
                    }
                    // for(auto v : edges[n2]) {
                    //     if(node_to_scc[n3] == node_to_scc[v]) {
                    //         return false;
                    //     }
                    // }
                }
            }
            if (cnb == degree - 1) {
                // TODO: we can apply vc_subset on n2 instead
                return false;
            }
        }

        node_t colored = 0;
        // the vertices that are in the current connected component
        vector<node_t> current;
        // the vertices that are in the bigger clique and smaller clique respectively
        vector<node_t> c1, c2;
        // check if and in which two cliques the neighbors of n are
        // keep track of the colored vertices
        unordered_map<node_t, int> colorArr;
        // Create a queue (FIFO) of vertex
        // numbers and enqueue source vertex
        // for BFS traversal
        queue <node_t> q;
        // this is needed because there might be different connected components
        for (auto v : g.get_succ(n)) {
            if(colorArr.find(v) == colorArr.end()) {
                current.clear();
                colorArr[v] = 1;
                colored = 1;
                q.push(v);

                // Run while there are vertices
                // in queue (Similar to BFS)
                while (!q.empty())
                {
                    node_t u = q.front();
                    current.push_back(u);
                    q.pop();

                    // Find all non-colored adjacent vertices
                    for (auto w : edges[u])
                    {
                        // destination w is not colored
                        if(colorArr.find(w) == colorArr.end()){
                            // Assign alternate color to this adjacent v of u
                            colorArr[w] = 1 - colorArr[u];
                            colored += colorArr[w];
                            q.push(w);
                        } else if(colorArr[w] == colorArr[u]) {
                            return false;
                        }
                    }
                }

                // check in which cliques the vertices are
                if(current.size() > 2*colored) {
                    // more than half the vertices are not colored
                    for(auto w : current) {
                        if(colorArr[w] == 0) {
                            if(edges[w].size() != 1) {
                                return false;
                            }
                            c1.push_back(w);
                        } else {
                            c2.push_back(w);
                        }
                    }
                } else {
                    // at most half the vertices are not colored
                    // note that if the number of vertices that are colored and uncolored are equal
                    // it matters neither for the checks nor for the later construction
                    // in when set we put them
                    // so this case does not need to be treated separately
                    for(auto w : current) {
                        if(colorArr[w] == 1) {
                            if(edges[w].size() != 1) {
                                return false;
                            }
                            c1.push_back(w);
                        } else {
                            c2.push_back(w);
                        }
                    }
                }

            }
        }
        node_t edge_sum = 0;
        for(auto p : edges) {
            edge_sum += p.second.size();
        }
        assert(c1.size()*2 == edge_sum);
        assert(c1.size() >= c2.size());
        // the neighbors of v are two cliques C1, C2 such that
        // for each c1 in C1 there is exactly one c2 in C2
        // such that c1 and c2 are not adjacent
        // also the SCC conditions hold
        // this is all we need
        vector<pair<node_t, node_t>> reconstruct_edges;
        vector<node_t> new_scc;
        for(auto v : c1) {
            if(node_to_scc[v] != node_to_scc[n]) {
                for(auto x : sccs[node_to_scc[v]]) {
                    new_scc.push_back(x);
                    node_to_scc[x] = node_to_scc[n];
                }
            }
            for(auto w : edges[v]) {
                for(auto x : g.get_succ(w)) {
                    if(v != x)
                        g.add_edge(v, x);
                }
                for(auto x : g.get_pred(w)) {
                    if(v != x)
                        g.add_edge(x, v);
                }
                if(node_to_scc[w] != node_to_scc[n]) {
                    for(auto x : sccs[node_to_scc[w]]) {
                        new_scc.push_back(x);
                        node_to_scc[x] = node_to_scc[n];
                    }
                }
                reconstruct_edges.emplace_back(v, w);
            }
        }
        for(auto w : c2) {
            g.remove(w);
        }
        // cout << n << " " << c1.size() << " " << c2.size() << endl;
        assert(reconstruct_edges.size() > 0);
        g.remove(n);
        sccs[node_to_scc[n]] = new_scc;
        reconstruct.push_back({n, INVALID_NODE, INVALID_NODE, INVALID_NODE, INVALID_NODE, false, false, true, move(reconstruct_edges)});
        return true;
    }

    bool apply_rule_11_or_12(Graph& g, node_t n,  vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc, vector<binary_reduced>& reconstruct) {
        // all edges of n must be bidirectional
        if(g.get_succ(n).size() > 4 || g.get_pred(n).size() > 4) {
            return false;
        }
        for(auto v : g.get_succ(n)) {
            if(g.get_pred(n).find(v) == g.get_pred(n).end()) {
                return false;
            }
        }
        // for this to work we cannot use SCC tricks
        // but it does work when the neighbors of n only have bidirectional edges
        for(auto w : g.get_succ(n)) {
            for(auto v : g.get_succ(w)) {
                if(g.get_pred(w).find(v) == g.get_pred(w).end()) {
                    return false;
                }
            }
            for(auto v : g.get_pred(w)) {
                if(g.get_succ(w).find(v) == g.get_succ(w).end()) {
                    return false;
                }
            }
        }

        node_t degree = g.get_succ(n).size();
        // we are looking for the case where we have exactly two edges
        pair<node_t, node_t> edge1 = make_pair(INVALID_NODE, INVALID_NODE), edge2 = make_pair(INVALID_NODE, INVALID_NODE);

        for (auto n2: g.get_succ(n)) {
            node_t cnb = 0;
            for (auto n3: g.get_succ(n)) {
                if (g.get_succ(n2).find(n3) != g.get_succ(n2).end()) {
                    // we need bidirectional edges
                    if(g.get_pred(n2).find(n3) == g.get_pred(n2).end()) {
                        return false;
                    }
                    if(n2 > n3) {
                        if(edge1.first == INVALID_NODE) {
                            edge1 = make_pair(n2,n3);
                        } else if(edge2.first == INVALID_NODE) {
                            edge2 = make_pair(n2, n3);
                        } else {
                            return false;
                        }
                    }
                    cnb++;
                }
            }
            if (cnb == degree - 1) {
                // TODO: we can apply vc_subset on n2 instead
                return false;
            }
        }
        if(edge2.first == INVALID_NODE) {
            return false;
        }
        // check whether rule 11 or rule 12 applies
        // rule 11: two disjoint edges
        if(edge1.first != edge2.first && edge1.first != edge2.second
           && edge1.second != edge2.first && edge1.second != edge2.second) {
            node_t a = edge1.first;
            node_t b = edge1.second;
            node_t c = edge2.first;
            node_t d = edge2.second;

            // Since we give the edges in a cycle, store last part and start from the back
            vector<node_t> store_succ(g.get_succ(a).begin(), g.get_succ(a).end());
            vector<node_t> store_pred(g.get_pred(a).begin(), g.get_pred(a).end());
            // transfer edges from c to a
            for(auto v : g.get_succ(c)) {
                if(v != a)
                    g.add_edge(a, v);
            }
            for(auto v : g.get_pred(c)) {
                if(v != a)
                    g.add_edge(v, a);
            }
            // transfer edges from b to c
            for(auto v : g.get_succ(b)) {
                if(v != c)
                    g.add_edge(c, v);
            }
            for(auto v : g.get_pred(b)) {
                if(v != c)
                    g.add_edge(v, c);
            }
            // transfer edges from d to b
            for(auto v : g.get_succ(d)) {
                if(v != b)
                    g.add_edge(b, v);
            }
            for(auto v : g.get_pred(d)) {
                if(v != b)
                    g.add_edge(v, b);
            }
            // transfer (stored) edges from a to d
            for (auto n2: store_succ) {
                if(n2 != d)
                    g.add_edge(n2, d);
            }
            for (auto n2: store_pred) {
                if(n2 != d)
                    g.add_edge(d, n2);
            }
            // make the vertices a clique and remove n
            g.add_edge(a,c);
            g.add_edge(c,a);
            g.add_edge(a,d);
            g.add_edge(d,a);
            g.add_edge(b,c);
            g.add_edge(c,d);
            g.add_edge(b,d);
            g.add_edge(d,b);
            g.remove(n);

            // update the SCCs
            vector<node_t> new_scc;
            for(auto w : {a,b,c}) {
                if(node_to_scc[w] != node_to_scc[d]) {
                    for(auto v : sccs[node_to_scc[w]]) {
                        sccs[node_to_scc[d]].push_back(v);
                        node_to_scc[v] = node_to_scc[d];
                    }
                }
            }
            sccs[node_to_scc[d]] = new_scc;
        } else {
            // rule 12: the edges share one vertex
            if(edge1.first == edge2.first) {
                swap(edge1.first, edge1.second);
            } else if(edge1.first == edge2.second) {
                swap(edge1.first, edge1.second);
                swap(edge2.first, edge2.second);
            } else if(edge1.second == edge2.second) {
                swap(edge2.first, edge2.second);
            }
            assert(edge1.second == edge2.first);
            node_t a = edge1.first;
            node_t b = edge1.second;
            node_t c = edge2.first;
            node_t d = INVALID_NODE;
            for(auto v : g.get_succ(n)) {
                if(v != a && v != b && v != c) {
                    d = v;
                }
            }

            // transfer edges from d to b
            for(auto v : g.get_succ(d)) {
                if(v != b)
                    g.add_edge(b, v);
            }
            for(auto v : g.get_pred(d)) {
                if(v != b)
                    g.add_edge(v, b);
            }
            // Since we give the edges in a cycle, store last part and start from the back
            vector<node_t> store_succ(g.get_succ(a).begin(), g.get_succ(a).end());
            vector<node_t> store_pred(g.get_pred(a).begin(), g.get_pred(a).end());
            // transfer edges from c to a
            for(auto v : g.get_succ(c)) {
                if(v != a)
                    g.add_edge(a, v);
            }
            for(auto v : g.get_pred(c)) {
                if(v != a)
                    g.add_edge(v, a);
            }
            // transfer edges from d to c
            for(auto v : g.get_succ(d)) {
                if(v != c)
                    g.add_edge(c, v);
            }
            for(auto v : g.get_pred(d)) {
                if(v != c)
                    g.add_edge(v, c);
            }
            // transfer (stored) edges from a to d
            for (auto n2: store_succ) {
                if(n2 != d)
                    g.add_edge(n2, d);
            }
            for (auto n2: store_pred) {
                if(n2 != d)
                    g.add_edge(d, n2);
            }
            // not sure if all of the removals are necessary
            g.remove_edge(a,b);
            g.remove_edge(b,a);
            g.remove_edge(a,c);
            g.remove_edge(c,a);
            g.remove_edge(a,d);
            g.remove_edge(d,a);
            g.add_edge(b,d);
            g.add_edge(d,b);
            g.add_edge(c,d);
            g.add_edge(d,c);
            g.remove(n);

            // update the SCCs
            vector<node_t> new_scc;
            for(auto w : {a,b,c}) {
                if(node_to_scc[w] != node_to_scc[d]) {
                    for(auto v : sccs[node_to_scc[w]]) {
                        sccs[node_to_scc[d]].push_back(v);
                        node_to_scc[v] = node_to_scc[d];
                    }
                }
            }
            sccs[node_to_scc[d]] = new_scc;
        }
        return true;
    }

    bool find_crown(Graph& g, vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc) {
        vector<node_t> in;
        for(node_t n = 0; n <= g.get_size(); n++) {
            if(g.is_deleted(n)) {
                continue;
            }
            if(sccs[node_to_scc[n]].size() > 1) {
                continue;
            }
            in.push_back(n);
        }
        vector<Glucose::Solver *> dummy;
        Glucose::Solver solver(dummy);
        unordered_map<node_t, node_t> node_to_var;
        Glucose::vec<Glucose::Lit> at_least_one;
        node_to_var.reserve(in.size());
        node_t i = 0;
        for(auto v : in) {
            // I(v)
            solver.newVar();
            // H(w)
            at_least_one.push(Glucose::mkLit(solver.newVar()));
            node_to_var.insert(make_pair(v, i));
            i++;
        }
        solver.addClause(at_least_one);
        i = 0;
        map<pair<node_t, node_t>, node_t> edge_to_match;
        for(auto v : in) {
            for(auto w : g.get_succ(v)) {
                auto it = node_to_var.find(w);
                if(it != node_to_var.end()) {
                    edge_to_match.emplace(make_pair(v, w), solver.newVar());
                }
            }
        }
        for(auto v : in) {
            // H(v) implies that M(v,w), i.e., one of the neighbors w is in the matching
            Glucose::vec<Glucose::Lit> match;
            match.push(Glucose::mkLit(2*node_to_var[v] + 1, true));

            for(auto w : g.get_succ(v)) {
                auto it = node_to_var.find(w);
                if(it != node_to_var.end()) {
                    // not I(v) or not I(w)
                    solver.addClause(Glucose::mkLit(2*node_to_var[v], true), Glucose::mkLit(2*(it->second), true));
                    // I(v) implies H(w)
                    solver.addClause(Glucose::mkLit(2*node_to_var[v], true), Glucose::mkLit(2*(it->second) + 1));
                    // H(v) implies that M(v,w), i.e., one of the neighbors w is in the matching
                    match.push(Glucose::mkLit(edge_to_match[make_pair(v,w)]));
                    // M(v,w) implies I(w) and not M(vp, w) for vp != v
                    solver.addClause(Glucose::mkLit(edge_to_match[make_pair(v,w)], true), Glucose::mkLit(2*node_to_var[w]));
                    for(auto vp : g.get_pred(w)) {
                        if(vp != v && node_to_var.find(vp) != node_to_var.end()) {
                            solver.addClause(Glucose::mkLit(edge_to_match[make_pair(v,w)], true), Glucose::mkLit(edge_to_match[make_pair(vp,w)], true));
                        }
                    }
                } else {
                    // there is a neighbor that isnt in
                    // so v cannot be in the independent set
                    solver.addClause(Glucose::mkLit(2*node_to_var[v], true));
                }
            }
            solver.addClause(match);
        }
        return solver.solve();
    }

    bool check_unconfined(Graph& g, node_t n, vector<vector<node_t>>& sccs, vector<node_t>& node_to_scc) {

        if(sccs[node_to_scc[n]].size() > 1) {
            return false;
        }
        set<node_t> S;
        set<node_t> neighbors;
        for(auto v : g.get_succ(n)) {
            if(sccs[node_to_scc[v]].size() > 1) {
                return false;
            }
            neighbors.insert(v);
        }
        S.insert(n);
        while(true) {
            node_t cur = INVALID_NODE;
            node_t include = INVALID_NODE;
            for(auto v : neighbors) {
                node_t in = 0;
                node_t cur_include = INVALID_NODE;
                for(auto w : g.get_succ(v)) {      
                    if(S.find(w) != S.end()) {
                        in++;
                        if(in > 1) 
                            break;
                    } else if(neighbors.find(w) == neighbors.end()) {
                        if(cur_include == INVALID_NODE) {
                            if(sccs[node_to_scc[w]].size() > 1) {
                                in = 5;
                                break;
                            }
                            for(auto np : g.get_succ(w)) {
                                if(sccs[node_to_scc[np]].size() > 1) {
                                    in = 5;
                                    break;
                                }
                            }                            
                            if(n == 5) {
                                break;
                            }
                            cur_include = w;
                        } else {
                            in = 5;
                            break;
                        }
                    }
                }
                if(in == 1) {
                    if(cur_include == INVALID_NODE) {
                        cur = v;
                        break;
                    } else if(cur == INVALID_NODE) {
                        cur = v;
                        include = cur_include;
                    }
                }
            }
            if(cur == INVALID_NODE) {
                return false;
            }
            if(include == INVALID_NODE) {
                return true;
            } 
            S.insert(include);
            for(auto w : g.get_succ(include)) {
                neighbors.insert(w);
            }
        }
    }

    bool domination(Graph& g, bool deep) {
        bool changed = false;
        for(node_t n=0; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;

            assert(g.get_succ(n).find(n) == g.get_succ(n).end());
            vector<node_t> tmp(g.get_succ(n).begin(), g.get_succ(n).end());
            for(auto to : tmp) {
                if((!deep && check_dominated(g, n, to))
                    || (deep && deep_check_dominated(g, n, to))) {
                    g.remove_edge(n, to);
                    changed = true;
                }
            }

        }

        vector<pair<node_t, node_t>> to_remove, biedges;
        for(node_t n=0; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;

            for(auto to : g.get_succ(n)) {
                if(g.get_pred(n).find(to) != g.get_pred(n).end()) {
                    biedges.push_back(make_pair(n, to));
                }
            }

        }
        for(auto p : biedges) {
            g.remove_edge(p.first, p.second);
        }
        vector<node_t> sccs = g.scc_idxs();
        for(node_t n=0; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;

            for(auto to : g.get_succ(n)) {
                if(sccs[n] != sccs[to]) {
                    to_remove.push_back(make_pair(n, to));
                    changed = true;
                }
            }

        }
        for(auto p :  to_remove) {
            g.remove_edge(p.first, p.second);
        }
        for(auto p : biedges) {
            g.add_edge(p.first, p.second);
        }
        return changed;
    }


    vector<node_t> preprocess(Graph& g, bool VC, vector<binary_reduced>& reconstruct) {
        vector<node_t> fixed;
        bool changed = true;
        node_t self_loops = 0;
        node_t degree0 = 0;
        node_t rule_7_nodes[4];
        vector<node_t> node_to_scc(g.get_size() + 1, 0);
        vector<vector<node_t>> sccs;

        while(changed) {
            // the following could be done more efficiently
            // make sure the edges between SCCS modulo two-cycles are removed
            changed = domination(g, false);
            // compute the sccs module two-cycles
            vector<pair<node_t, node_t>> biedges;
            for(node_t n=0; n <= g.get_size(); n++) {
                if (g.is_deleted(n))
                    continue;

                for(auto to : g.get_succ(n)) {
                    if(g.get_pred(n).find(to) != g.get_pred(n).end()) {
                        biedges.push_back(make_pair(n, to));
                    }
                }

            }
            for(auto p : biedges) {
                g.remove_edge(p.first, p.second);
            }
            sccs = g.sccs();
            for(auto p : biedges) {
                g.add_edge(p.first, p.second);
            }
            // construct the node to scc mapping
            for(node_t i = 0; i < sccs.size(); i++) {
                for(auto v : sccs[i]) {
                    node_to_scc[v] = i;
                }
            }
            for(node_t n=0; n <= g.get_size(); n++) {
                if (g.is_deleted(n))
                    continue;

                if (g.get_succ(n).find(n) != g.get_succ(n).end()) {
                    fixed.push_back(n);
                    self_loops++;
                    g.remove(n);
                    changed = true;
                } else if (g.get_succ(n).empty() || g.get_pred(n).empty()) {
                    g.remove(n);
                    degree0++;
                    changed = true;
                    // } else if (g.get_succ(n).size() == 1) {
                    //      node_t cn = *g.get_succ(n).begin();
                    //      for (auto n2 : g.get_pred(n))
                    //          g.add_edge(n2, cn);
                    //      g.remove(n);
                    //      degree2++;
                    //      changed = true;
                    // } else if (g.get_pred(n).size() == 1) {
                    //      node_t cn = *g.get_pred(n).begin();
                    //      for(auto n2:g.get_succ(n))
                    //          g.add_edge(cn, n2);
                    //      g.remove(n);
                    //      degree2++;
                    //      changed = true;

                } else if (g.get_succ(n).size() == 1 || g.get_pred(n).size() == 1 || check_indiclique(g, n) || check_outdiclique(g,n) || check_diclique2(g,n) || check_diclique3(g,n)) {
                    vector<node_t> to_remove;
                    for(auto n1 : g.get_pred(n)) {
                        for(auto n2 : g.get_succ(n)) {
                            if(n1 == n2) {
                                to_remove.push_back(n1);
                            } else {
                                g.add_edge(n1, n2);
                            }
                        }
                    }
                    for(auto v : to_remove) {
                        g.remove(v);
                        fixed.push_back(v);
                        self_loops++;
                    }
                    g.remove(n);
                    //degree2++;
                    changed = true;
                } else if(check_vc_degree_one(g,n)) {
                    fixed.push_back(*g.get_succ(n).begin());
                    g.remove(*g.get_succ(n).begin());
                    g.remove(n);
                    changed = true;
                } else if(check_vc_subset(g, n)) {
                    fixed.push_back(n);
                    g.remove(n);
                    changed = true;
                } else if(VC && check_double(g, n, node_to_scc)) {
                    node_t first = *g.get_succ(n).begin();
                    node_t second = *(++g.get_succ(n).begin());
                    g.remove(n);
                    for(auto v : g.get_succ(first)) {
                        assert(v != second);
                        g.add_edge(second, v);
                    }
                    for(auto v : g.get_pred(first)) {
                        assert(v != second);
                        g.add_edge(v, second);
                    }
                    g.remove(first);
                    changed = true;
                    reconstruct.push_back({n, first, second, INVALID_NODE, INVALID_NODE});
                    // update the node to scc mapping
                    // may be an overapproximation, i.e., if x,y are in the same scc according to this they still might not be
                    // but this way of overapproximating only makes it so that we do not know that we can apply a rule even though we could
                    // but not the other way around, which would be problematic
                    for(auto v : sccs[node_to_scc[first]]) {
                        if(v != first) {
                            sccs[node_to_scc[second]].push_back(v);
                            node_to_scc[v] = node_to_scc[second];
                        }
                    }
                } else if(VC && check_rule_6(g, n, node_to_scc)) {
                    auto it = g.get_succ(n).begin();
                    node_t a = *it;
                    node_t b = *(++it);
                    node_t c = *(++it);
                
                    // Since we give the edges in a cycle, store last part
                    vector<node_t> store_succ(g.get_succ(a).begin(), g.get_succ(a).end());
                    vector<node_t> store_pred(g.get_pred(a).begin(), g.get_pred(a).end());
                    // transfer edges from b to a
                    for(auto v : g.get_succ(b)) {
                        assert(v != a);
                        g.add_edge(a, v);
                    }
                    for(auto v : g.get_pred(b)) {
                        assert(v != a);
                        g.add_edge(v, a);
                    }
                    // transfer edges from c to b
                    for(auto v : g.get_succ(c)) {
                        assert(v != b);
                        g.add_edge(b, v);
                    }
                    for(auto v : g.get_pred(c)) {
                        assert(v != b);
                        g.add_edge(v, b);
                    }
                    // transfer (stored) edges from a to c
                    for (auto n2: store_succ) {
                        assert(n2 != c);
                        g.add_edge(n2, c);
                    }
                    for (auto n2: store_pred) {
                        assert(n2 != c);
                        g.add_edge(c, n2);
                    }

                    g.remove(n);

                    // add the extra bidirectional edges
                    g.add_edge(a, b);
                    g.add_edge(b, a);
                    g.add_edge(b, c);
                    g.add_edge(c, b);

                    reconstruct.push_back({n, a, b, c, INVALID_NODE, true});
                    changed = true;
                    // update the node to scc mapping
                    // may be an overapproximation, i.e., if x,y are in the same scc according to this they still might not be
                    // but this way of overapproximating only makes it so that we do not know that we can apply a rule even though we could
                    // but not the other way around, which would be problematic

                    // TODO: if the sccs are size one we can get a better approximation
                    // we just take the union of all the sccs
                    if(node_to_scc[a] != node_to_scc[c]) {
                        for(auto v : sccs[node_to_scc[a]]) {
                            sccs[node_to_scc[c]].push_back(v);
                            node_to_scc[v] = node_to_scc[c];
                        }
                    }
                    if(node_to_scc[b] != node_to_scc[c]) {
                        for(auto v : sccs[node_to_scc[b]]) {
                            sccs[node_to_scc[c]].push_back(v);
                            node_to_scc[v] = node_to_scc[c];
                        }
                    }
                } else if(VC && check_rule_72(g, n, node_to_scc, rule_7_nodes)) {
                    node_t d = rule_7_nodes[0];

                    // transfer the edges between d and its neighbors to the other nodes
                    for (node_t i = 1; i < 4; i++) {
                        for(auto v : g.get_succ(d)) {
                            g.add_edge(rule_7_nodes[i], v);
                            assert(v != rule_7_nodes[0]);
                            assert(v != rule_7_nodes[1]);
                            assert(v != rule_7_nodes[2]);
                            assert(v != rule_7_nodes[3]);
                        }
                        for(auto v : g.get_pred(d)) {
                            g.add_edge(v, rule_7_nodes[i]);
                            assert(v != rule_7_nodes[0]);
                            assert(v != rule_7_nodes[1]);
                            assert(v != rule_7_nodes[2]);
                            assert(v != rule_7_nodes[3]);
                        }
                    }

                    g.remove(d);
                    g.remove(n);

                    reconstruct.push_back({n, rule_7_nodes[3], rule_7_nodes[2], rule_7_nodes[1], d, true, true});
                    changed = true;
                    // update the node to scc mapping
                    // may be an overapproximation, i.e., if x,y are in the same scc according to this they still might not be
                    // but this way of overapproximating only makes it so that we do not know that we can apply a rule even though we could
                    // but not the other way around, which would be problematic

                    // TODO: if the sccs are size one we can get a better approximation
                    // we just take the union of all the sccs
                    vector<node_t> new_scc;
                    unordered_set<node_t> taken;
                    for(node_t i = 0; i < 4; i++) {
                        if(taken.find(rule_7_nodes[i]) == taken.end()) {
                            taken.insert(node_to_scc[rule_7_nodes[i]]);
                            for(auto v : sccs[node_to_scc[rule_7_nodes[i]]]) {
                                new_scc.push_back(v);
                                node_to_scc[v] = node_to_scc[d];
                            }
                        }
                    }
                    sccs[node_to_scc[d]] = new_scc;
                } else if(VC && apply_rule_71(g, n, sccs, node_to_scc, reconstruct)) {
                    changed = true;
                } else if(VC && apply_rule_4_or_5(g, n, sccs, node_to_scc, reconstruct)) {
                    changed = true;
                } else if(VC && apply_rule_8(g, n, sccs, node_to_scc, reconstruct)) {
                    changed = true;
                // } else if(VC && apply_rule_11_or_12(g, n, sccs, node_to_scc, reconstruct)) {
                //     changed = true;
                // } else if(check_unconfined(g, n, sccs, node_to_scc)) {
                //     fixed.push_back(n);
                //     g.remove(n);
                //     changed = true;
                }
            }
        }

        // for(node_t n = 0; n <= g.get_size(); n++) {
        //     if(!g.is_deleted(n)) {
        //         cout << g.disjoint_cycles(n).size() << endl;
        //     }
        // }
        // if (VERBOSITY > 0) {
        //     cout << "Self Loops: " << self_loops << ", Degree 0: " << degree0 << ", Degree 2: " << degree2 << endl;
        // }

        return fixed;
    }

    vector<pair<node_t, node_t>> preprocess2(Graph& g) {
        vector<pair<node_t, node_t>> ret;

        for(node_t n=0; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;
            for(node_t v1 : g.get_succ(n)) {
                for(node_t v2 : g.get_succ(n)) {
                    if(v1 != v2) {
                        if(check_subset(g, v1, v2)) {
                            ret.emplace_back(v1,v2);
                        }
                    }
                }

            }
        }
        return ret;
    }

}
#endif //CPP_PREPROCESSING_H