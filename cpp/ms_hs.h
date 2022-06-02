//
// Created by aschidler on 5/10/22.
//

#ifndef CPP_MS_HS_H
#define CPP_MS_HS_H
#include "../external/EvalMaxSAT/lib/EvalMaxSAT/src/EvalMaxSAT.h"
#include "graph.h"
#include "preprocessing.h"
#include <set>
#include "dfvs.h"
#include "heuristic.h"
#include "sat_encode.h"

namespace dfvs {
    void apply_binary_reduction(Graph& g, vector<vector<node_t>>& cycles, vector<node_t>& pre_included, vector<binary_reduced>& reconstruct) {
        // Check if graph really has no non-binary cycles
        VcGraph vc(g.get_size());
        vector<bool> fixed(g.get_size() + 1);
        vector<bool> included(g.get_size() + 1);
        vector<vector<node_t>> large_cycles;
        vector<unordered_set<size_t>> node_to_cycle(g.get_size() + 1);
        bool rebuild = false;

        for(auto i=0; i < cycles.size(); i++) {
            auto& cc = cycles[i];
            if (cc.size() == 2) {
                vc.add_edge(cc[0], cc[1]);
            } else {
                large_cycles.push_back(cc);
                for(auto n:cc) {
                    fixed[n] = true;
                    node_to_cycle[n].insert(i);
                    for(auto n2: cc) {
                        if (n > n2)
                            vc.add_edge(n, n2, true);
                    }
                }
            }
        }

        bool changed = true;
        bool second_round = false;
        while (changed || second_round) {
            changed = false;
            for (node_t n = 1; n <= g.get_size(); n++) {
                bool pp = false;

                if (vc.is_deleted(n) || fixed[n])
                    continue;

                // Degree 1
                if (vc.degree(n) == 1) {
                    auto n2 = *vc.get_adjacency(n).begin();
                    vc.remove_vertex(n);
                    vc.remove_vertex(n2);
                    g.remove(n);
                    g.remove(n2);
                    included[n2] = true;
                    pre_included.push_back(n2);
                    fixed[n2] = false;

                    // TODO: This should work, but produces wrong results...
                    for(auto& idx : node_to_cycle[n2]) {
                        for(auto u : cycles[idx]) {
                            if (u != n2) {
                                node_to_cycle[u].erase(idx);
                                if (node_to_cycle[u].empty()) {
                                    fixed[u] = false;
                                }
                            }
                        }
                        for(auto u : cycles[idx]) {
                            if (u != n2) {
                                for (auto v: cycles[idx]) {
                                    if (u < v && n2 != v) {
                                        if (!vc.check_long_cycle(u, v)) {
                                            vc.remove_edge(u, v);
                                        } else {
                                            assert(vc.adjacent(u ,v));
                                        }
                                    }
                                }
                            }
                        }
                    }

                    changed = true;
                    pp = true;
                } else { // Check if neighborhood subsumes
                    bool removed = false;
                    vc.add_edge(n, n);

                    for (auto n2: vc.get_adjacency(n)) {
                        if (n == n2)
                            continue;

                        if (std::includes(vc.get_adjacency(n).begin(), vc.get_adjacency(n).end(), vc.get_adjacency(n2).begin(),
                                          vc.get_adjacency(n2).end())) {
                            pre_included.push_back(n);
                            vc.remove_vertex(n);
                            g.remove(n);
                            included[n] = true;
                            removed = true;
                            changed = true;
                            break;
                        }
                    }
                    if (!removed) {
                        vc.remove_edge(n, n);
                    }
                    pp = removed;
                }

                if (! pp) {
                    if (vc.degree(n) == 2) {
                        auto it = vc.get_adjacency(n).begin();
                        node_t u = *it++;
                        node_t v = *it;

                        if (!fixed[u] && !fixed[v] && !vc.adjacent(u, v)) {
                            vc.transfer_edges(u, v);
                            vc.remove_vertex(u);
                            vc.remove_vertex(n);
                            g.remove(u);
                            g.remove(n);
                            reconstruct.push_back({n, u, v, INVALID_NODE, INVALID_NODE});
                            changed = true;
                            rebuild = true;
                        }
                    }
                    else if (vc.degree(n) == 3) {
                        bool eligible = true;
                        for (auto n2: vc.get_adjacency(n)) {
                            if (fixed[n2])
                                eligible = false;
                        }
                        if (! eligible)
                            continue;

                        auto it = vc.get_adjacency(n).begin();
                        node_t a = *(it++);
                        node_t b = *(it++);
                        node_t c = *it;
                        assert(a!= b && b != c && a != c);
                        if (vc.degree(a) == 1 || vc.degree(b) == 1 || vc.degree(c) == 1)
                            continue;

                        node_t edges = 0;
                        for(auto n1: vc.get_adjacency(n)) {
                            for(auto n2: vc.get_adjacency(n)) {
                                if (n2 > n1 && vc.adjacent(n1, n2)) {
                                    edges++;
                                }
                            }
                        }

                        if (edges == 1) { // Special case rule 5
                            // Make c the one not adjacent to a or b
                            if (vc.adjacent(a, c)) {
                                swap(b, c);
                            } else if (!vc.adjacent(a, b)) {
                                swap(a, c);
                            }
                            assert(!vc.adjacent(a, c) && !vc.adjacent(b, c));
                            vc.transfer_edges(c, a);
                            vc.transfer_edges(c, b);
                            vc.remove_vertex(c);
                            vc.remove_vertex(n);
                            g.remove(n);
                            g.remove(c);
                            reconstruct.push_back({n, a, b, c, INVALID_NODE});
                            changed = true;
                            rebuild = true;
                        }
                        else if (edges == 0) { // Reduction 6
                            // Since we give the edges in a cycle a->b, b->c, c->a, store last part
                            vector<node_t> store(vc.get_adjacency(a).begin(), vc.get_adjacency(a).end());
                            vc.transfer_edges(b, a);
                            vc.transfer_edges(c, b);
                            for (auto n2: store)
                                vc.add_edge(n2, c);

                            vc.remove_vertex(n);
                            g.remove(n);

                            vc.add_edge(a, b);
                            vc.add_edge(b, c);
                            reconstruct.push_back({n, a, b, c, INVALID_NODE, true});
                            changed = true;
                            rebuild = true;
                        }
                    }
                    else if (vc.degree(n) == 4) {
                        node_t edges = 0;
                        bool subsumed = false;
                        bool any_fixed = false;

                        for(auto n1 : vc.get_adjacency(n)) {
                            node_t these_edges = 0;
                            any_fixed = any_fixed || fixed[n1] || vc.degree(n1) == 1;
                            for(auto n2: vc.get_adjacency(n)) {
                                if (n1 != n2 && vc.adjacent(n1, n2))
                                    these_edges++;
                            }
                            if (these_edges == 3) {
                                subsumed = true;
                                break;
                            } else {
                                edges += these_edges;
                            }
                        }
                        edges /= 2;
                        if (subsumed || any_fixed)
                            continue;

                        auto it = vc.get_adjacency(n).begin();
                        node_t a = *(it++);
                        node_t b = *(it++);
                        node_t c = *(it++);
                        node_t d = *(it++);

                        if (edges == 4) { // Special Case reduction 4
                            // Sort so no edge between a,b and c,d exists
                            if (!vc.adjacent(a, c))
                                swap(b, c);
                            else if (!vc.adjacent(a, d))
                                swap(b, d);
                            assert(!vc.adjacent(a, b) && !vc.adjacent(c, d));
                            // DANGER!
                            vc.transfer_edges(a, b);
                            vc.transfer_edges(c, d);
                            vc.remove_vertex(a);
                            vc.remove_vertex(c);
                            vc.remove_vertex(n);

                            g.remove(a);
                            g.remove(c);
                            g.remove(n);
                            reconstruct.push_back({n, a, b, c, d});
                            changed = true;
                            rebuild = true;
                        }
                        else if (edges == 3) { // Reduction 7
                            vector<pair<node_t, vector<node_t>>> local_adj;
                            local_adj.reserve(3);

                            bool any_zero = false;
                            for (auto n1: vc.get_adjacency(n)) {
                                vector<node_t> la;
                                for (auto n2: vc.get_adjacency(n)) {
                                    if (n2 != n1 && vc.adjacent(n1, n2))
                                        la.push_back(n2);
                                }
                                if (la.empty())
                                    any_zero = true;
                                local_adj.emplace_back(n1, la);
                            }

                            if (any_zero) { // Reduction 7.2
                                changed = true;
                                rebuild = true;
                                for (auto &centry : local_adj) {
                                    if (centry.second.empty() && centry.first != local_adj.back().first) {
                                        swap(centry, local_adj.back());
                                    }
                                }

                                d = local_adj.back().first;

                                for (auto &centry: local_adj) {
                                    if (centry.first != d) {
                                        vc.transfer_edges(d, centry.first);
                                    }
                                }

                                vc.remove_vertex(d);
                                vc.remove_vertex(n);

                                g.remove(n);
                                g.remove(d);
                                reconstruct.push_back({n, local_adj[0].first, local_adj[1].first, local_adj[2].first, local_adj[3].first, true, true});///
                            }
                            else { // Reduction 7.1
                                if (local_adj[0].second.size() != 1) {
                                    if (local_adj[1].second.size() == 1)
                                        swap(local_adj[0], local_adj[1]);
                                    else {
                                        swap(local_adj[0], local_adj[2]);
                                    }
                                }

                                if (local_adj[3].second.size() != 1) {
                                    if (local_adj[1].second.size() == 1)
                                        swap(local_adj[3], local_adj[1]);
                                    else {
                                        swap(local_adj[3], local_adj[2]);
                                    }
                                }

                                if (local_adj[0].second.front() != local_adj[1].first)
                                    swap(local_adj[1], local_adj[2]);

                                a = local_adj[0].first;
                                b = local_adj[1].first;
                                c = local_adj[2].first;
                                d = local_adj[3].first;

                                vector<node_t> tmp(vc.get_adjacency(a).begin(), vc.get_adjacency(a).end());

                                vc.transfer_edges(b, a);
                                vc.transfer_edges(d, a);
                                vc.transfer_edges(d, b);

                                for(auto n2: tmp) {
                                    if (n2 != c)
                                        vc.add_edge(c, n2);
                                    if (n2 != d)
                                        vc.add_edge(d, n2);
                                }

                                // Make a,b,c,d a clique, i.e. 3 out of 4 will be in the VC
                                vc.add_edge(a, d);
                                vc.add_edge(a, c);
                                vc.add_edge(b, d);

                                assert(vc.adjacent(a, b) && vc.adjacent(a, c) && vc.adjacent(a, d) && vc.adjacent(b, c) && vc.adjacent(b, d) && vc.adjacent(c, d));

                                reconstruct.push_back({n, a, b, c, d, true, false});
                                rebuild = true;
                                vc.remove_vertex(n);
                                g.remove(n);
                                changed = true;
                                rebuild = true;
                            }
                        }
                    }
                    else if (second_round){
                        bool any_fixed = false;
                        bool is_subsumed = false;
                        node_t twice = INVALID_NODE;
                        vector<pair<node_t, node_t>> edges;
                        edges.reserve(vc.degree(n) * (vc.degree(n) - 2) / 2);

                        for (auto n2: vc.get_adjacency(n)) {
                            if (fixed[n2] || vc.degree(n2) == 1) {
                                any_fixed = true;
                                break;
                            }
                            node_t cnb = 0;
                            for (auto n3: vc.get_adjacency(n)) {
                                if (vc.adjacent(n2, n3)) {
                                    cnb++;
                                } else if (n2 < n3) {
                                    edges.emplace_back(n2, n3);
                                }
                            }
                            if (cnb == vc.degree(n) - 1) {
                                is_subsumed = true;
                            } else if (cnb == vc.degree(n) - 3) {
                                twice = n2;
                            }
                        }

                        if (! any_fixed && !is_subsumed && (vc.degree(n) + 1) / 2 == edges.size()) {
                            if (vc.degree(n) % 2 == 1) {
                                assert(twice != INVALID_NODE);
                                for (auto &cedge: edges) {
                                    if (cedge.second == twice)
                                        swap(cedge.first, cedge.second);
                                    if (cedge.first == twice)
                                        vc.transfer_edges(twice, cedge.second);
                                }
                                g.remove(twice);
                                vc.remove_vertex(twice);
                            }

                            vc.remove_vertex(n);
                            g.remove(n);

                            for(auto& cedge : edges) {
                                if (cedge.first != twice) {
                                    vc.transfer_edges(cedge.first, cedge.second);
                                    vc.remove_vertex(cedge.first);
                                    g.remove(cedge.first);
                                }
                            }
                            reconstruct.push_back({n, twice, INVALID_NODE, INVALID_NODE, INVALID_NODE, false, false, false, move(edges)});
                            changed = true;
                            rebuild = true;
                        }
                    }
                }
            }

            if (! changed && !second_round)
                second_round = true;
            else if (second_round)
                second_round = false;
        }

        if (VERBOSITY > 0) {
            cout << "Binary preprocessing pre-selected: " << pre_included.size() + reconstruct.size() << endl;
        }

        for (node_t n=1; n <= g.get_size(); n++) {
            if (vc.get_adjacency(n).empty() && !g.is_deleted(n)) {
                g.remove(n);
            }
        }

        if (rebuild || !pre_included.empty()) {
            for (auto n: pre_included)
                g.remove(n);

            // Remove the auxiliary adjacencies created for >2-cycles
            for(auto& cc: large_cycles) {
                for(auto n: cc) {
                    for(auto n2: cc) {
                        if (n != n2 && vc.check_long_cycle(n, n2, false))
                            vc.remove_edge(n, n2);
                    }
                }
            }

            // Create all remaining 2-cycles
            cycles.clear();
            for (node_t n=1; n <= g.get_size(); n++) {
                for (auto n2: vc.get_adjacency(n)) {
                    if (n < n2)
                        cycles.push_back({n, n2});
                }
            }

            // Add large cycles that have not been invalidated
            for(auto& cc: large_cycles) {
                bool invalid = false;

                for (auto n: cc)
                    invalid = invalid || included[n];
                if (!invalid)
                    cycles.push_back(cc);
            }
        }

        if (VERBOSITY > 0)
            cout << "Binary preprocessing reduced cycles: " << cycles.size() << endl;
    }

    vector<node_t> ms_hs_run(Graph& g2, vector<binary_reduced>& reconstruct) {
        // copy graph, so we can verify dfvs in main call
        Graph g = g2.copy();

        vector<vector<node_t>> cycles;
        vector<node_t> result;
        auto tcycles = g.find_short_cycles(cycles, 2, false);
        bool all_cycles = false;

        // Remove the edges between binary cycles, this makes finding non-subsumed cycles way faster
        // It also allows to check if there are no cycles larger than 2
        auto gx = g2.copy();
        for(auto& cc: cycles) {
            gx.remove_edge(cc[0], cc[1]);
            gx.remove_edge(cc[1], cc[0]);
        }

        // Perform special vertex cover reduction
        vector<node_t> pre_included;
        if (gx.is_acyclic(pre_included)) {// pre_included is just an empty dummy set
            apply_binary_reduction(g, cycles, pre_included, reconstruct);
        } else {
            auto ecycles = gx.find_short_cycles(cycles, 3, false);
            auto three_cycle_idx = cycles.size();
            // Apply extended VC preprocessing for large graph, with few larger cycles
            auto g_nodes = g.get_nodes();
            bool be_hopeful = true;
            if (tcycles > g_nodes && ecycles < tcycles && ecycles < tcycles / 2) {
                node_t last_result=ecycles;
                for(node_t climit = 4; climit < 10; climit++) {
                    auto new_result = gx.find_short_cycles(cycles, climit, true);
                    if (new_result > last_result + 20) {
                        be_hopeful = false;
                        break;
                    }
                    if (new_result == 0 && gx.find_non_subsumed_cycle(cycles).empty())
                        break;
                    last_result = new_result;
                }
                // We need all cycles, otherwise reduction will not to be correct
                all_cycles = false;
                if (be_hopeful) {
                    auto new_cycle = gx.find_non_subsumed_cycle(cycles);
                    for(int i=0; !new_cycle.empty() && i < 25; i++) {
                        cycles.push_back(new_cycle);
                        new_cycle = gx.find_non_subsumed_cycle(cycles);
                    }
                    if (new_cycle.empty())
                        all_cycles = true;
                }

                if (all_cycles){
                    apply_binary_reduction(g, cycles, pre_included, reconstruct);
                } else if (VERBOSITY > 0) {
                    cout << "Not binary reducible" << endl;
                    cycles.erase(cycles.begin() + three_cycle_idx, cycles.end());
                }
            }
        }

        if (!all_cycles && g.get_nodes() < 5000) {
            for (int i = 4; i < 8; i++) {
                if (cycles.size() > 2000)
                    break;
                gx.find_short_cycles(cycles, i, true);
            }
        }

        vector<int> vars(g.get_size());
        node_t i = 1;
        for(node_t n=0; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                vars[n] = i++;
            }
        }

        vector<set<node_t>> succ(g.get_nodes() + 1, set<node_t>());
        vector<set<node_t>> pred(g.get_nodes() + 1, set<node_t>());
        for(node_t n=0; n <= g.get_size(); n++) {
            if(! g.is_deleted(n)) {
                for(auto v : g.get_succ(n)) {
                    succ[vars[n]].insert(vars[v]);
                }
                for(auto v : g.get_pred(n)) {
                    pred[vars[n]].insert(vars[v]);
                }
            }
        }

        vector<set<node_t>> dummy;
        //initial_sol.clear();
        EvalMaxSAT slv(0, all_cycles ? dummy : succ, all_cycles ? dummy : pred, pred.size());

        //slv->setTimeOutFast(180);


        for(node_t n=0; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                int res = slv.newVar();
                assert(vars[n] == res);
                slv.addWeightedClause({vars[n]}, 1);
            }
        }

//        vector<int> is_source(g.get_size()+1);
//        vector<int> is_drain(g.get_size()+1);
//        vector<int> is_noncounting(g.get_size()+1);

        auto add_helper_clauses = [&] (const unordered_set<node_t>& nodes, node_t target, bool is_succ, node_t limit2) {
            vector<int> clause;
//            vector<int> clause2;
//            bool any_possible = false;
//            bool all_special = true;
//
            for (node_t n : nodes) {
//                if (is_noncounting[n] > 0) {
//                    clause2.push_back(-is_noncounting[n]);
//                    any_possible = true;
//                } else
//                    clause2.push_back(vars[n]);

                clause.push_back(vars[n]);
//                if (is_succ) {
//                    if (is_noncounting[n] > 0)
//                        slv.addClause({-is_noncounting[n], -is_drain[target]});
//                    else
//                        slv.addClause({-vars[n], -is_drain[target]});
//                } else {
//                    if (is_noncounting[n] > 0) {
//                        slv.addClause({-is_noncounting[n], -is_source[target]});
//                    } else {
//                        slv.addClause({-vars[n], -is_source[target]});
//                    }
//                }
            }
//            if (is_succ) {
//                clause.push_back(is_drain[target]);
//            } else {
//                clause.push_back(is_source[target]);
//            }

            clause.push_back(vars[target]);
            slv.addClause(clause);

//            if (any_possible)
//                slv.addClause(clause2);
        };

        // Add some guiding clauses, may lead to massive slowdown
        if (! all_cycles) {
            const node_t helper_limit = 0;
            const node_t helper2_limit = 0;

//            for (node_t n = 0; n <= g.get_size(); n++) {
//                if (!g.is_deleted(n)) {
//                    vector<int> rev_clause;
//                    if (g.get_succ(n).size() <= helper_limit){
//                        is_drain[n] = slv.newVar();
//                        is_noncounting[n] = slv.newVar();
//                        slv.addClause({vars[n], is_noncounting[n]});
//                        slv.addClause({-is_drain[n], is_noncounting[n]});
//                        slv.addClause({-is_drain[n], vars[n]});
//                        rev_clause.push_back(is_drain[n]);
//                    }
//                    if (g.get_pred(n).size() <= helper_limit) {
//                        if (is_noncounting[n] == 0) {
//                            is_noncounting[n] = slv.newVar();
//                            slv.addClause({vars[n], is_noncounting[n]});
//                        }
//                        is_source[n] = slv.newVar();
//                        slv.addClause({-is_source[n], is_noncounting[n]});
//                        slv.addClause({-is_source[n], vars[n]});
//                        rev_clause.push_back(is_source[n]);
//                    }
//                    if(! rev_clause.empty()) {
//                        rev_clause.push_back(-is_noncounting[n]);
//                        rev_clause.push_back(-vars[n]);
//                        slv.addClause(rev_clause);
//                    }
//                }
//            }

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && g.get_succ(n).size() <= helper_limit)
                    add_helper_clauses(g.get_succ(n), n, true, helper2_limit);
                if (!g.is_deleted(n) && g.get_pred(n).size() <= helper_limit)
                    add_helper_clauses(g.get_pred(n), n, false, helper2_limit);
            }
        }

        // if(true) {
        //     vector<pair<node_t, node_t>> pairs = preprocess2(g);
        //     for(auto p : pairs) {
        //         vector<int> clause;
        //         clause.push_back(vars[p.first]);
        //         clause.push_back(-1 * vars[p.second]);
        //         slv.addClause(clause);
        //     }
        // }

        for(auto& cc : cycles) {
            vector<int> clause;
            clause.reserve(cc.size());

            for (auto n : cc)
                clause.push_back(-1 * vars[n]);

            slv.addClause(clause);
         }


        bool is_valid = false;
        size_t last_round = SIZE_MAX;
        while (! is_valid) {
            bool solved = slv.solve();
            assert(solved);
            result.clear();
            result.reserve(slv.getCost());
            if (VERBOSITY > 0)
                cout << "Found hitting set of size " << slv.getCost() << endl;

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && slv.getValue(vars[n]) == 0) {
                    result.push_back(n);
                }
            }

            if (! pre_included.empty()) {
                result.insert(result.end(), std::begin(pre_included), std::end(pre_included));
            }

            vector<node_t> cfvs(result);
            node_t added = 0;
            node_t added_sum = 0;
            size_t limit = last_round < 50 ? 100 : 1;
            last_round = 0;

            vector<node_t> new_cycle = g.find_cycle(cfvs);
            if(!new_cycle.empty()) {
                if (g.get_nodes() < 1000) {
                    Graph cur = g.copy();
                    Graph gp = g.copy();
                    for (auto v : cfvs) {
                        cur.remove(v);
                        gp.remove(v);
                        //cout << v << " ";
                    }
                    //cout << endl;
                    while (gp.get_nodes() > 0) {
                        vector<binary_reduced> dummy;
                        size_t cnt = 0;
                        for (auto v : preprocess(gp, false, dummy)) {
                            cnt = 0;
                            for (const auto& c_cycle : cur.disjoint_cycles(v)) {
                                vector<int> new_clause;
                                new_clause.reserve(c_cycle.size());
                                for (auto cn: c_cycle) {
                                    new_clause.push_back(-vars[cn]);
                                }
                                slv.addClause(new_clause);
                                added++;
                                last_round++;
                                added_sum += new_clause.size();
                                if (++cnt > limit)
                                    break;
                            }
                            cfvs.push_back(v);
                        }

                        auto some_cycle = g.find_cycle(cfvs);
                        if (some_cycle.empty())
                            break;
                        node_t c_max = INVALID_NODE;
                        node_t c_max_node = INVALID_NODE;
                        for(node_t nx =1 ; nx <= gp.get_size(); nx++) {
                            if (! gp.is_deleted(nx)) {
                                if (min(gp.get_succ(nx).size(),gp.get_pred(nx).size()) < c_max) {
                                    c_max_node = nx;
                                    c_max = min(gp.get_succ(nx).size(),gp.get_pred(nx).size());
                                }
                            }
                        }

                        cnt = 0;
                        for (const auto& n_cycle : cur.disjoint_cycles(c_max_node)) {
                            vector<int> new_clause;
                            new_clause.reserve(n_cycle.size());
                            for(auto cn : n_cycle) {
                                new_clause.push_back(-vars[cn]);
                            }
                            slv.addClause(new_clause);
                            added++;
                            added_sum += new_clause.size();
                            last_round++;
                            if (++cnt > limit)
                                break;
                        }
                        cfvs.push_back(c_max_node);
                        gp.remove(c_max_node);
                    }
                } else {
                    vector<int> new_clause;
                    new_clause.reserve(new_cycle.size());
                    for (auto cn: new_cycle) {
                        new_clause.push_back(-vars[cn]);
                    }
                    added++;
                    added_sum += new_cycle.size();
                    slv.addClause(new_clause);
                    cfvs.insert(cfvs.end(), new_cycle.begin(), new_cycle.end());
                    new_cycle = g.find_cycle(cfvs);
                }
            }
            

            if (added > 0) {
                if (VERBOSITY > 0)
                    cout << "Found and added " << added << " cycles, with " << added_sum << " atoms." << endl;
            } else {
                is_valid = true;
            }
        }

        return result;
    }
}

#endif //CPP_MS_HS_H
