#include <iostream>
#include "graph.h"
#include "preprocessing.h"
#include "ms_hs.h"
#include <chrono>
#include "sat_encode.h"
#include "dfvs.h"

using std::chrono::high_resolution_clock;
using std::chrono::duration_cast;
using std::chrono::duration;
using std::chrono::seconds;
#include "bb.h"

/**
 * Removes superfluous edges, does not do much, code for reference
 * @param g
 */
void test_pp(dfvs::Graph& g) {
    vector<vector<node_t>> cycles;
    g.find_short_cycles(cycles, 2, false);
    vector<vector<bool>> used_edges(g.get_size()+1, vector<bool>(g.get_size()+1));

    auto gx = g.copy();
    for(auto& cc: cycles) {
        gx.remove_edge(cc[0], cc[1]);
        gx.remove_edge(cc[1], cc[0]);
        used_edges[cc[0]][cc[1]] = true;
        used_edges[cc[1]][cc[0]] = true;
    }

    cycles.clear();
    for(int i=3; i < 5; i++) {
        gx.find_short_cycles(cycles, i, true);
    }

    for(auto& cc: cycles) {
        for(int i=0; i < cc.size(); i++) {
            if (i != 0)
                used_edges[cc[i]][cc[i-1]] = true;
            else
                used_edges[cc[0]][cc[cc.size()-1]] = true;
        }
    }

    bool all_edges = gx.find_non_subsumed_cycle(cycles).empty();

    node_t cnt = 0;
    node_t cnt2 = 0;
    for(node_t n=1; n <= g.get_size(); n++) {
        for (auto n2: gx.get_succ(n)) {
            if (!used_edges[n][n2]) {
                cnt++;
                if (!all_edges) {
//                    if (!gx.find_elementary_cycle_with_edge(n, n2, used_edges)) {
//                        cnt2++;
//                        cout << "Unused edge" << endl;
//                    }
                } else {
                    g.remove_edge(n, n2);
//                        changed = true;
//                        break;
                }
            }
        }
    }
    cout << cnt << " Superfluous edge candidates, " << cnt2 << " holds." << endl;
}

int main() {
    auto t1 = high_resolution_clock::now();
    auto g = dfvs::parse();
    auto verifier = g.copy();
    // if (VERBOSITY > 0)
    //     cout << g.get_nodes() << " Nodes, " << g.get_edges() << " Edges" << std::endl;
    vector<dfvs::binary_reduced> reconstruct;
    auto preselected = dfvs::preprocess(g, true, reconstruct);
    if (VERBOSITY > 0)
        cout << g.get_nodes() << " Nodes, " << g.get_edges() << " Edges" << std::endl;

    auto result = (g.get_nodes() > 0) ? dfvs::ms_hs_run(g, reconstruct) : vector<node_t>();
    //auto result = dfvs::encode_sat_sd(g, false);
    unsigned int before = result.size();
    result.insert(result.end(), preselected.begin(), preselected.end());

    if(! reconstruct.empty()) {
            vector<bool> as_set(g.get_size()+1);
            for(auto n : result) {
                as_set[n] = true;
            }

            for(auto it = reconstruct.rbegin(); it != reconstruct.rend(); ++it) {
                auto& entry = *it;
                if (! entry.is_rule6or7) {
                    if (entry.edges.empty()) {
                        if (entry.c == INVALID_NODE) {
                            if (as_set[entry.b]) {
                                as_set[entry.a] = true;
                            } else {
                                as_set[entry.n] = true;
                            }
                        } else if (entry.d == INVALID_NODE) {
                            if (as_set[entry.a] && as_set[entry.b]) {
                                as_set[entry.c] = true;
                            } else {
                                as_set[entry.n] = true;
                            }
                        } else {
                            if (as_set[entry.b] && as_set[entry.d]) {
                                as_set[entry.a] = true;
                                as_set[entry.c] = true;
                            } else {
                                as_set[entry.n] = true;
                                if (as_set[entry.b])
                                    as_set[entry.a] = true;
                                else if (as_set[entry.d])
                                    as_set[entry.c] = true;
                            }
                        }
                    } else if(!entry.is_rule8) { // General case for d(d-2)/2
                        bool twice_found = false;
                        for(auto& cedge : entry.edges) {
                            if (as_set[cedge.second]) {
                                if (cedge.first == entry.a && !twice_found) {
                                    twice_found = true;
                                } else {
                                    as_set[cedge.first] = true;
                                }
                            } else {
                                assert(! as_set[entry.n]);
                                as_set[entry.n] = true;
                            }
                        }
                    } else {
                        node_t remove_again = INVALID_NODE;
                        for(auto& cedge : entry.edges) {
                            if(as_set[cedge.first]) {
                                as_set[cedge.second] = true;
                            } else {
                                as_set[entry.n] = true;
                                assert(remove_again == INVALID_NODE);
                                remove_again = cedge.second;
                            }
                        }
                        if(remove_again != INVALID_NODE) {
                            as_set[remove_again] = false;
                        }
                    }
                } else {
                    if (entry.d == INVALID_NODE) { // Rule 6, degree 3
                        if (!(as_set[entry.a] && as_set[entry.b] && as_set[entry.c])) {
                            as_set[entry.n] = true;
                            if (as_set[entry.a] && as_set[entry.c]) {
                                as_set[entry.c] = false;
                            } else if (as_set[entry.a] && as_set[entry.b]) {
                                as_set[entry.a] = false;
                            } else if (as_set[entry.b] && as_set[entry.c]) {
                                as_set[entry.b] = false;
                            } else {
                                assert(as_set[entry.b]);
                                as_set[entry.b] = false;
                            }
                        }
                    } else {
                        if (! entry.is_empty_case) { // Rule 7.1
                            if (! (as_set[entry.a] && as_set[entry.b] && as_set[entry.c] && as_set[entry.d])) {
                                as_set[entry.n] = true;
                                if (as_set[entry.a] && as_set[entry.c] && as_set[entry.d]) {
                                    as_set[entry.d] = false;
                                } else if (as_set[entry.a] && as_set[entry.b] && as_set[entry.d]) {
                                    as_set[entry.a] = false;
                                } else if (as_set[entry.b] && as_set[entry.c] && as_set[entry.d]) {
                                    as_set[entry.d] = false;
                                } else if (as_set[entry.a] && as_set[entry.b] && as_set[entry.c]) {
                                    as_set[entry.a] = false;
                                } else {
                                    assert(false);
                                }
                            }
                        } else { // Rule 7.2
                            if (as_set[entry.a] && as_set[entry.b] && as_set[entry.c]) {
                                as_set[entry.d] = true;
                            } else {
                                as_set[entry.n] = true;
                            }
                        }
                    }
                }
            }

            result.clear();
            for(node_t n=1; n < as_set.size(); n++) {
                if (as_set[n])
                    result.push_back(n);
            }
        }

    if (VERBOSITY == 0) {
        if(!verifier.find_cycle(result).empty()) {
            cerr << "This is not a FVS." << endl;
            exit(-1);
        }
        for (auto n: result) {
            cout << n << endl;
        }
    } else {
        unordered_set<node_t> cc(result.begin(), result.end());
        cout << cc.size() << endl;
        if (verifier.is_acyclic(result)) {
            cout << "Found DFVS: "<<  result.size() << " PP-Size: " << preselected.size() << ", DFVS-Size : " << before << endl;
        } else {
            cout << "Invalid Result " << result.size() << " (PP: "<< preselected.size() << ")" << endl;
        }
        auto t2 = high_resolution_clock::now();
        /* Getting number of milliseconds as an integer. */
        auto ms_int = duration_cast<seconds>(t2 - t1);
        std::cout << ms_int.count() << " seconds\n";
    }
    return 0;
}
