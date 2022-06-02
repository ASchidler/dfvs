//
// Created by aschidler on 5/19/22.
//

#ifndef CPP_BB_H
#define CPP_BB_H
#include "graph.h"
#include "dfvs.h"
#include "preprocessing.h"
#include <queue>

namespace dfvs {
    pair<bool, vector<node_t>> bnb_rec(Graph& g, node_t c_result, node_t best_result, node_t try_short, node_t depth, vector<bool>& c_set) {
        vector<node_t> cycle;
//        node_t max_n = INVALID_NODE;
//        node_t max_d = 0;
//        for(node_t n =1 ; n <= g.get_size() + 1; n++) {
//            if (! g.is_deleted(n) && min(g.get_succ(n).size(), g.get_pred(n).size()) > max_d) {
//                max_n = n;
//                max_d = min(g.get_succ(n).size(), g.get_pred(n).size());
//            }
//        }
//        auto cycles = g.disjoint_cycles(max_n);
//        vector<node_t> cycle;
//        for(auto& cc: cycles) {
//            if (cycle.empty() || cycle.size() > cc.size())
//                cycle = move(cc);
//        }
//        if (try_short < 10) {
//            vector<vector<node_t>> cycles;
//            for (; try_short < 10; try_short++) {
//                g.find_short_cycles(cycles, try_short, false);
//                if (!cycles.empty()) {
//                    cycle = cycles[0];
//                    break;
//                }
//            }
//        }
        if (cycle.empty())
            cycle = g.find_cycle(c_set);

        if (cycle.empty()) {
            if (VERBOSITY > 0)
                cout << "Success " << c_result << endl;
            return {true, {}};
        }

        vector<binary_reduced> dummy;
        pair<bool, vector<node_t>> result = {false, {}};

        for(auto n: cycle) {
            node_t in_cnt = 0;
            for(auto n2: g.get_pred(n)) {
                if (! c_set[n2]) {
                    if (++in_cnt >= 2)
                        break;
                }
            }
            if (in_cnt < 2)
                continue;
            node_t out_cnt = 0;
            for(auto n2: g.get_succ(n)) {
                if (! c_set[n2]) {
                    if (++out_cnt >= 2)
                        break;
                }
            }
            if (out_cnt < 2)
                continue;

            //auto preselect = preprocess(g2, false, dummy);
            c_set[n] = true;
            if (c_result + 1 + g.find_disjoint_short_cycles(10, c_set) >= best_result) {
                //cout << "Prune " << depth << endl;
                c_set[n] = false;
                continue;
            }
            auto result2 = bnb_rec(g, c_result + 1, best_result, try_short, depth + 1, c_set);
            c_set[n] = false;
            if (result2.first) {
                result = result2;
                result.second.push_back(n);
                //result.second.insert(result.second.begin(), preselect.begin(), preselect.end());
                best_result = c_result + result.second.size();
            }
        }
        return result;
    }
    void bnb(Graph& g) {
        vector<node_t> c_nodes;
        vector<vector<node_t>> cycles;
        vector<bool> found_nodes(g.get_size() + 1);
        cout << "LB " << g.find_disjoint_short_cycles(11, found_nodes) << endl;
        node_t node_count = 0;
        node_t all_nodes = g.get_nodes();
        for(node_t i=2; i < 11 && node_count < all_nodes; i++) {
            g.find_short_cycles(cycles, i, true);
        }
        auto ub = greedy_hs(cycles, g.get_size());
        cout << "UB " << ub.size() << endl;
        vector<bool> cycles_hit(cycles.size());
        vector<bool> c_set(g.get_size() + 1);
        auto result = bnb_rec(g, 0, ub.size(), 2, 0, c_set);
        cout << "Finished " << result.second.size() << endl;
    }

    void greedy_exact(Graph& g) {
        priority_queue<pair<node_t, vector<bool>>, std::vector<pair<node_t, vector<bool>>>, std::greater<>> q;
        q.emplace(0, vector<bool>(g.get_size() + 1));

        while(! q.empty()) {
            auto c_el = q.top();
            q.pop();

            auto cycle = g.find_cycle(c_el.second);

            if (cycle.empty()) {
                if (VERBOSITY > 0)
                    cout << "Success " << c_el.first << endl;
                return;
            }

            vector<binary_reduced> dummy;
            pair<bool, vector<node_t>> result = {false, {}};

            for(auto n: cycle) {
                node_t in_cnt = 0;
                for(auto n2: g.get_pred(n)) {
                    if (! c_el.second[n2]) {
                        if (++in_cnt >= 2)
                            break;
                    }
                }
                if (in_cnt < 2)
                    continue;
                node_t out_cnt = 0;
                for(auto n2: g.get_succ(n)) {
                    if (! c_el.second[n2]) {
                        if (++out_cnt >= 2)
                            break;
                    }
                }
                if (out_cnt < 2)
                    continue;

                auto n_sol = vector<bool>(c_el.second);
                n_sol[n] = true;
                q.emplace(c_el.first + 1 + g.find_disjoint_short_cycles(10, n_sol), move(n_sol));
            }
        }
    }
}

#endif //CPP_BB_H
