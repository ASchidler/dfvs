//
// Created by asc on 11.05.22.
//

#ifndef CPP_SAT_ENCODE_H
#define CPP_SAT_ENCODE_H
#include "../external/EvalMaxSAT/lib/EvalMaxSAT/src/EvalMaxSAT.h"
#include "graph.h"
#include "preprocessing.h"

namespace dfvs {
    vector<node_t> encode_sat_conn(Graph& g) {
        vector<node_t> result;
        auto slv = new EvalMaxSAT(0);
        vector<vector<int>> connected(g.get_size()+1, vector<int>(g.get_size()+1));
        vector<int> in_set(g.get_size()+1);

        for(node_t n=1; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                in_set[n] = slv->newVar();
                slv->addWeightedClause({-in_set[n]},1);
                for(node_t n2=1; n2 <= g.get_size(); n2++) {
                    if (! g.is_deleted(n2)) {
                        connected[n][n2] = slv->newVar();
                    }
                }
                slv->addClause({-connected[n][n]});
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            for(node_t n2=1; n2 <= g.get_size(); n2++) {
                for(node_t n3=1; n3 <= g.get_size(); n3++) {
                    if (!g.is_deleted(n) && !g.is_deleted(n2) && !g.is_deleted(n3))
                        slv->addClause({-connected[n][n2], -connected[n2][n3], connected[n][n3]});
                }
            }
        }
        for(node_t n=1; n <= g.get_size(); n++) {
            for(auto n2: g.get_succ(n)) {
                slv->addClause({in_set[n], connected[n][n2]});
            }
        }

        // Some superfluous clauses
//        for(node_t n=1; n <= g.get_size(); n++) {
//            if (g.is_deleted(n))
//                continue;
//            vector<int> clause;
//            clause.reserve(g.get_succ(n).size()+1);
//            for(auto n2: g.get_succ(n)) {
//                clause.push_back(-in_set[n2]);
//            }
//            clause.push_back(-in_set[n]);
//            assert(clause.size() > 1);
//            slv->addClause(clause);
//        }
//        for(node_t n=1; n <= g.get_size(); n++) {
//            if (g.is_deleted(n))
//                continue;
//            vector<int> clause;
//            clause.reserve(g.get_pred(n).size()+1);
//            for(auto n2: g.get_pred(n)) {
//                clause.push_back(-in_set[n2]);
//            }
//            clause.push_back(-in_set[n]);
//            slv->addClause(clause);
//        }

        for(node_t n=1; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;
            if (g.get_succ(n).size() == 2) {
                for (auto n2: g.get_succ(n)) {
                    slv->addClause({-in_set[n2], -in_set[n]});
                }
            } else if (g.get_succ(n).size() == 3) {
                auto it = g.get_succ(n).begin();
                auto u = *it++;
                auto v = *it++;
                auto w = *it;

                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
            }
            if (g.get_pred(n).size() == 2) {
                for (auto n2: g.get_pred(n)) {
                    slv->addClause({-in_set[n2], -in_set[n]});
                }
            } else if (g.get_pred(n).size() == 3) {
                auto it = g.get_pred(n).begin();
                auto u = *it++;
                auto v = *it++;
                auto w = *it;

                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
            }
        }

        if (slv->solve()) {
            result.reserve(slv->getCost());
            if (VERBOSITY > 0)
                cout << "Found hitting set of size " << slv->getCost() << endl;

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && slv->getValue(in_set[n])) {
                    result.push_back(n);
                }
            }
        }

        return result;
    }

    vector<node_t> encode_sat_ord(Graph& g, bool add_cycles) {
        vector<node_t> result;

        auto slv = new EvalMaxSAT(0);
        vector<vector<int>> ord(g.get_size()+1, vector<int>(g.get_size()+1));
        vector<int> in_set(g.get_size()+1);
        auto _ord= [&](node_t x, node_t y) {
            if (x < y)
                return ord[x][y];
            else
                return -ord[y][x];
        };
        for(node_t n=1; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                in_set[n] = slv->newVar();
                slv->addWeightedClause({-in_set[n]},1);
                for(node_t n2=n+1; n2 <= g.get_size(); n2++) {
                    if (! g.is_deleted(n2)) {
                        ord[n][n2] = slv->newVar();
                    }
                }
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            for(node_t n2=1; n2 <= g.get_size(); n2++) {
                for(node_t n3=1; n3 <= g.get_size(); n3++) {
                    if (n != n2 && n != n3 && n2 != n3 && !g.is_deleted(n) && !g.is_deleted(n2) && !g.is_deleted(n3))
                        slv->addClause({-_ord(n, n2), -_ord(n2, n3), _ord(n, n3)});
                }
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            for(auto n2: g.get_succ(n)) {
                slv->addClause({_ord(n, n2), in_set[n]});
            }
        }

        // Some superfluous clauses, expressed the preprocessing, whenever the in-degree/out-degree becomes <= 1
//        for(node_t n=1; n <= g.get_size(); n++) {
//            if (g.is_deleted(n))
//                continue;
//            if (g.get_succ(n).size() == 2) {
//                for (auto n2: g.get_succ(n)) {
//                    slv->addClause({-in_set[n2], -in_set[n]});
//                }
//            }
//            else if (g.get_succ(n).size() == 3) {
//                auto it = g.get_succ(n).begin();
//                auto u = *it++;
//                auto v = *it++;
//                auto w = *it;
//
//                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
//                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
//                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
//            }
//            if (g.get_pred(n).size() == 2) {
//                for (auto n2: g.get_pred(n)) {
//                    slv->addClause({-in_set[n2], -in_set[n]});
//                }
//            }
//            else if (g.get_pred(n).size() == 3) {
//                auto it = g.get_pred(n).begin();
//                auto u = *it++;
//                auto v = *it++;
//                auto w = *it;
//
//                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
//                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
//                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
//            }
//        }

        // Symmetry Breaking - Order vertices lexicographically within DFVS
        for(node_t n=1; n <= g.get_size(); n++) {
            for (node_t n2 = 1; n2 <= g.get_size(); n2++) {
                if (! g.is_deleted(n) && !g.is_deleted((n2))) {
                    if (n != n2) {
                        // Lexicographical ordering within dfvs
                        if (n < n2) {
                            slv->addClause({-in_set[n2], _ord(n, n2)});
                        } else {
                            slv->addClause({-in_set[n], in_set[n2], _ord(n2, n)});
                        }
                    }
                }
            }
        }

        // Symmetry Breaking - Order DFVS vertices after all non-DFVS vertices
        for(node_t n=1; n <= g.get_size(); n++) {
            for (node_t n2 = 1; n2 <= g.get_size(); n2++) {
                if (n != n2) {
                    if (! g.is_deleted(n) && !g.is_deleted((n2))) {
                        // push dfvs to the end

                    }
                }
            }
        }

        if (add_cycles) {
            vector<vector<node_t>> cycles;
            g.find_short_cycles(cycles, 2, false);
            g.find_short_cycles(cycles, 3, true);

            for(auto& cc : cycles) {
                vector<int> clause;
                clause.reserve(cc.size());

                for (auto n : cc)
                    clause.push_back(in_set[n]);

                slv->addClause(clause);
            }
        }

        if (slv->solve()) {
            result.clear();
            result.reserve(slv->getCost());
            if (VERBOSITY > 0)
                cout << "Found hitting set of size " << slv->getCost() << endl;

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && slv->getValue(in_set[n])) {
                    result.push_back(n);
                }
            }
        }

        if (VERBOSITY > 0)
            cout << "Done" << endl;

        return result;
    }


    vector<node_t> encode_sat_ord2(Graph& g, bool add_cycles) {
        vector<node_t> result;

        vector<vector<node_t>> cycles;
        g.find_short_cycles(cycles, 2, false);

        // Remove the edges between binary cycles, this makes finding non-subsumed cycles way faster
        // It also allows to check if there are no cycles larger than 2
        for(auto& cc: cycles) {
            g.remove_edge(cc[0], cc[1]);
            g.remove_edge(cc[1], cc[0]);
        }

        for(node_t climit = 4; climit < 6; climit++) {
            g.find_short_cycles(cycles, climit, true);
        }

        EvalMaxSAT slv(0);
        vector<int> in_set(g.get_size()+1);
        for(node_t n=1; n <= g.get_size(); n++) {
            if (!g.is_deleted(n)) {
                in_set[n] = slv.newVar();
                slv.addWeightedClause({-in_set[n]}, 1);
            }
        }

        vector<vector<int>> ord(g.get_size()+1, vector<int>(g.get_size()+1));
        auto _ord= [&](node_t x, node_t y) {
            if (x < y)
                return ord[x][y];
            else
                return -ord[y][x];
        };

        for(node_t n=1; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                vector<node_t> nb;
                nb.reserve(g.get_succ(n).size() + g.get_pred(n).size() + 1);
                nb.insert(nb.end(), g.get_pred(n).begin(), g.get_pred(n).end());
                nb.insert(nb.end(), g.get_succ(n).begin(), g.get_succ(n).end());
                nb.push_back(n);

                for(node_t n1 : nb) {
                    for(node_t n2: nb) {
                        if (n1 < n2) {
                            if (_ord(n1, n2) == 0) {
                                ord[n1][n2] = slv.newVar();
                                slv.addClause({-in_set[n2], _ord(n1, n2)});
                                slv.addClause({-in_set[n1], in_set[n2], _ord(n2, n1)});
                            }
                        }
                    }
                }
                for(node_t n1 : nb) {
                    for (node_t n2: nb) {
                        if (n1 != n2) {
                            for (node_t n3: nb) {
                                if (n1 != n3 && n2 != n3) {
                                    slv.addClause({-_ord(n1, n2), -_ord(n2, n3), _ord(n1, n3)});
                                }
                            }
                        }
                    }
                }
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            for(auto n2: g.get_succ(n)) {
                slv.addClause({_ord(n, n2), in_set[n]});
            }
        }

        // Some superfluous clauses, expressed the preprocessing, whenever the in-degree/out-degree becomes <= 1
//        for(node_t n=1; n <= g.get_size(); n++) {
//            if (g.is_deleted(n))
//                continue;
//            if (g.get_succ(n).size() == 2) {
//                for (auto n2: g.get_succ(n)) {
//                    slv->addClause({-in_set[n2], -in_set[n]});
//                }
//            }
//            else if (g.get_succ(n).size() == 3) {
//                auto it = g.get_succ(n).begin();
//                auto u = *it++;
//                auto v = *it++;
//                auto w = *it;
//
//                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
//                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
//                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
//            }
//            if (g.get_pred(n).size() == 2) {
//                for (auto n2: g.get_pred(n)) {
//                    slv->addClause({-in_set[n2], -in_set[n]});
//                }
//            }
//            else if (g.get_pred(n).size() == 3) {
//                auto it = g.get_pred(n).begin();
//                auto u = *it++;
//                auto v = *it++;
//                auto w = *it;
//
//                slv->addClause({-in_set[u], -in_set[v], -in_set[n]});
//                slv->addClause({-in_set[v], -in_set[w], -in_set[n]});
//                slv->addClause({-in_set[u], -in_set[w], -in_set[n]});
//            }
//        }
//
//        // Symmetry Breaking - Order vertices lexicographically within DFVS
//        for(node_t n=1; n <= g.get_size(); n++) {
//            for (node_t n2 = n+1; n2 <= g.get_size(); n2++) {
//                if (! g.is_deleted(n) && !g.is_deleted((n2))) {
//                    // Lexicographical ordering within dfvs
//                    slv->addClause({-in_set[n], -in_set[n2], _ord(n, n2)});
//                }
//            }
//        }
//
//        // Symmetry Breaking - Order DFVS vertices after all non-DFVS vertices
//        for(node_t n=1; n <= g.get_size(); n++) {
//            for (node_t n2 = 1; n2 <= g.get_size(); n2++) {
//                if (n != n2) {
//                    if (! g.is_deleted(n) && !g.is_deleted((n2))) {
//                        // push dfvs to the end
//                        slv->addClause({in_set[n], -in_set[n2], _ord(n, n2)});
//                    }
//                }
//            }
//        }

        bool is_valid = false;

        while(! is_valid) {
            if (slv.solve()) {
                result.clear();
                result.reserve(slv.getCost());
                if (VERBOSITY > 0)
                    cout << "Found hitting set of size " << slv.getCost() << endl;

                for (node_t n = 0; n <= g.get_size(); n++) {
                    if (!g.is_deleted(n) && slv.getValue(in_set[n])) {
                        result.push_back(n);
                    }
                }

                if (g.is_acyclic(result)) {
                    is_valid = true;
                } else {
                    vector<node_t> c_dfvs(result);
                    auto c_cycle = g.find_cycle(c_dfvs);
                    size_t cnt = 0;
                    while (!c_cycle.empty()) {
                        c_dfvs.insert(c_dfvs.end(), c_cycle.begin(), c_cycle.end());
                        auto n1 = c_cycle[1];
                        auto n2 = c_cycle.back();
                        auto n3 = c_cycle[0];
                        assert(g.get_pred(n1).find(n2) == g.get_pred(n1).end() && g.get_succ(n1).find(n2) == g.get_succ(n1).end());
                        assert(c_cycle.size() > 3);
                        assert(n1 != n2 && n2 != n3 && n1 != n3);
                        c_cycle.clear();
                        c_cycle.push_back(n1);
                        c_cycle.push_back(n2);
                        c_cycle.push_back(n3);
                        for(node_t n1 : c_cycle) {
                            for(node_t n2: c_cycle) {
                                if (n1 < n2) {
                                    if (_ord(n1, n2) == 0) {
                                        ord[n1][n2] = slv.newVar();
                                        slv.addClause({-in_set[n2], _ord(n1, n2)});
                                        slv.addClause({-in_set[n1], in_set[n2], _ord(n2, n1)});
                                        cnt++;
                                    }
                                }
                            }
                        }
                        for(node_t n1 : c_cycle) {
                            for (node_t n2: c_cycle) {
                                if (n1 != n2) {
                                    for (node_t n3: c_cycle) {
                                        if (n1 != n3 && n2 != n3) {
                                            slv.addClause({-_ord(n1, n2), -_ord(n2, n3), _ord(n1, n3)});
                                        }
                                    }
                                }
                            }
                        }
//                        vector<int> c_clause;
//                        c_clause.reserve(c_cycle.size());
//                        for(auto n: c_clause)
//                            c_clause.push_back(in_set[n]);
//                        slv->addClause(c_clause);

                        c_cycle = g.find_cycle(c_dfvs);
                    }
                    cout << "Failure " << cnt << endl;
                }
            }
        }

        if (VERBOSITY > 0)
            cout << "Done" << endl;

        return result;
    }

    vector<node_t> encode_sat_num(Graph &g, bool add_cycles) {
        vector<node_t> result;
        node_t cycle_limit = g.get_size();
        EvalMaxSAT slv(0);
        vector<vector<int>> vertex_num(g.get_size()+1, vector<int>(g.get_size()+1));
        vector<int> in_set(g.get_size()+1);

        vector<vector<node_t>> cycles;

        for(node_t n=1; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                in_set[n] = slv.newVar();
                slv.addWeightedClause({-in_set[n]},1);
                for(node_t num=0; num < cycle_limit; num++) {
                    vertex_num[n][num] = slv.newVar();
                    if (num > 0)
                        slv.addClause({-vertex_num[n][num], vertex_num[n][num - 1]});
                }
                slv.addClause({-in_set[n], -vertex_num[n][0]});
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            if (g.is_deleted(n))
                continue;

            slv.addClause({-vertex_num[n][cycle_limit-1]});

            for(auto n2: g.get_succ(n)) {
                slv.addClause({in_set[n], in_set[n2], vertex_num[n2][1]});
                for(node_t num=0; num < cycle_limit-1; num++) {
                    slv.addClause({in_set[n2], -vertex_num[n][num], vertex_num[n2][num+1]});
                }
            }

//            // Break symmetries
//            for(node_t num=1; num < cycle_limit; num++) {
//                vector<int> clause;
//                clause.reserve(g.get_pred(n).size() + 1);
//                clause.push_back(-vertex_num[n][num]);
//                for (auto n2: g.get_pred(n)) {
//                    clause.push_back(-vertex_num[n2][num-1]);
//                }
//                slv.addClause(clause);
//            }
        }

        if (add_cycles) {
            cycles.clear();
            g.find_short_cycles(cycles, 2, false);
            g.find_short_cycles(cycles, 3, true);

            for(auto& cc : cycles) {
                vector<int> clause;
                clause.reserve(cc.size());

                for (auto n : cc)
                    clause.push_back(in_set[n]);

                slv.addClause(clause);
            }
        }

        if (slv.solve()) {
            result.clear();
            result.reserve(slv.getCost());
            if (VERBOSITY > 0)
                cout << "Found hitting set of size " << slv.getCost() << endl;

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && slv.getValue(in_set[n])) {
                    result.push_back(n);
                }
            }
        }

        if (VERBOSITY > 0)
            cout << "Done" << endl;

        return result;
    }

    vector<node_t> encode_sat_sd(Graph &g, bool add_cycles) {
        vector<node_t> result;
        EvalMaxSAT slv(0);
        vector<int> in_set(g.get_size()+1);
        vector<int> is_source(g.get_size()+1);
        vector<int> is_safe(g.get_size()+1);
        vector<int> is_drain(g.get_size()+1);

        vector<vector<node_t>> cycles;

        for(node_t n=1; n <= g.get_size(); n++) {
            if (! g.is_deleted(n)) {
                in_set[n] = slv.newVar();
                is_source[n] = slv.newVar();
                is_safe[n] = slv.newVar();
                is_drain[n] = slv.newVar();
                slv.addWeightedClause({-in_set[n]},1);

                slv.addClause({-is_drain[n], is_safe[n]});
                slv.addClause({-is_source[n], is_safe[n]});
                slv.addClause({-in_set[n], is_safe[n]});
                slv.addClause({-is_safe[n], is_drain[n], is_source[n], -in_set[n]});
            }
        }

        for(node_t n=1; n <= g.get_size(); n++) {
            if (!g.is_deleted(n)) {
                vector<int> clause;
                for(auto n2: g.get_succ(n)) {
                    clause.push_back(-in_set[n2]);
                    slv.addClause({in_set[n2], -is_drain[n]});
                }
                clause.push_back(is_drain[n]);
                slv.addClause(clause);

                vector<int> clause2;
                for(auto n2: g.get_pred(n)) {
                    clause2.push_back(-in_set[n2]);
                    slv.addClause({in_set[n2], -is_source[n]});
                }
                clause2.push_back(is_source[n]);
                slv.addClause(clause2);

                vector<int> clause3;
                for(auto n2: g.get_pred(n)) {
                    clause3.push_back(-is_safe[n2]);
                    slv.addClause({is_safe[n2], -is_safe[n]});
                }
                clause3.push_back(is_safe[n]);
                slv.addClause(clause3);
            }
        }

        if (slv.solve()) {
            result.clear();
            result.reserve(slv.getCost());
            if (VERBOSITY > 0)
                cout << "Found hitting set of size " << slv.getCost() << endl;

            for (node_t n = 0; n <= g.get_size(); n++) {
                if (!g.is_deleted(n) && slv.getValue(in_set[n])) {
                    result.push_back(n);
                }
            }
        }

        if (VERBOSITY > 0)
            cout << "Done" << endl;

        return result;
    }

}
#endif //CPP_SAT_ENCODE_H
