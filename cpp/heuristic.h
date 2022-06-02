//
// Created by asc on 18.05.22.
//

#ifndef CPP_HEURISTIC_H
#define CPP_HEURISTIC_H
#include "dfvs.h"
#include <vector>

using namespace std;

namespace dfvs {
    vector<node_t> greedy_hs(vector<vector<node_t>>& cycles, node_t nodes) {
        vector<pair<size_t, vector<size_t>>> node_to_cycle(nodes+1, {0, vector<size_t>()});
        vector<bool> cycles_matched(cycles.size());
        vector<node_t> solution;

        for(auto i=0; i < cycles.size(); i++) {
            for(auto n: cycles[i]) {
                node_to_cycle[n].first++;
                node_to_cycle[n].second.push_back(i);
            }
        }

        while(true) {
            size_t c_max = 0;
            node_t c_max_node = INVALID_NODE;
            for(node_t n=1; n <= nodes; n++) {
                if (node_to_cycle[n].first > c_max) {
                    c_max = node_to_cycle[n].first;
                    c_max_node = n;
                }
            }

            if (c_max_node == INVALID_NODE)
                break;

            for(auto idx: node_to_cycle[c_max_node].second) {
                if (!cycles_matched[idx]) {
                    cycles_matched[idx] = true;
                    for(auto n2: cycles[idx]) {
                        if (node_to_cycle[n2].first > 0)
                            node_to_cycle[n2].first--;
                    }
                }
                node_to_cycle[c_max_node].first = 0;
            }
            solution.push_back(c_max_node);
        }
        return solution;
    }
}
#endif //CPP_HEURISTIC_H
