//
// Created by aschidler on 5/10/22.
//

#ifndef CPP_GRAPH_H
#define CPP_GRAPH_H
#include <vector>
#include <unordered_set>
#include "dfvs.h"
#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <assert.h>
#include <limits.h>
#include <queue>
#include <string.h>
#include <map>
#include <stack>
#include <set>
#include <set>
#include <unordered_map>

using namespace std;

namespace dfvs {
    class Graph {
    public:
        explicit Graph(node_t size) : _succ(size + 1), _pred(size + 1), _size(size), _deleted(size+1){
            _deleted[0] = true;
        }

        Graph(vector<unordered_set<node_t>> succ, vector<unordered_set<node_t>> pred, vector<bool> deleted) :
                _succ(succ.begin(), succ.end()), _pred(pred.begin(), pred.end()), _size(succ.size() - 1), _deleted(deleted.begin(), deleted.end()){

        }

        void add_edge(node_t n1, node_t n2) {
            _succ[n1].insert(n2);
            _pred[n2].insert(n1);
        }

        void remove_edge(node_t n1, node_t n2) {
            _succ[n1].erase(n2);
            _pred[n2].erase(n1);
        }

        [[nodiscard]] Graph copy() const {
            Graph g2(_succ, _pred, _deleted);
            return g2;
        }

        [[nodiscard]] node_t get_size() const {
            return _size;
        }

        [[nodiscard]] node_t get_nodes() const {
            node_t cnt = 0;

            for(node_t n=0; n <= _size; n++) {
                if (! _deleted[n])
                    cnt++;
            }

            return cnt;
        }

        [[nodiscard]] uint32_t get_edges() const {
            uint32_t result = 0;
            for (auto& edges : _succ ) {
                result += edges.size();
            }

            return result;
        }

        // TODO: the collection returned should be immutable...
        const unordered_set<node_t>& get_succ(node_t n){
            return _succ[n];
        }

        const unordered_set<node_t>& get_pred(node_t n) {
            return _pred[n];
        }

        [[nodiscard]] bool is_deleted(node_t vertex) const {
            return _deleted[vertex];
        }

        void remove(node_t vertex) {
            for(auto n2:_succ[vertex])
                _pred[n2].erase(vertex);
            _succ[vertex].clear();

            for(auto n2: _pred[vertex])
                _succ[n2].erase(vertex);
            _pred[vertex].clear();
            _deleted[vertex] = true;
        }

        bool find_disjoint_short_cycles_rec(node_t start, node_t cn, node_t c_limit, vector<bool>& found_nodes) {
            found_nodes[cn] = true;

            if (_succ[cn].find(start) != _succ[cn].end()) {
                if (c_limit == 1) {
                    return true;
                }
            } else if (c_limit > 1) {
                for (auto n: _succ[cn]) {
                    if (!found_nodes[n]) {
                        if (find_disjoint_short_cycles_rec(start, n, c_limit - 1, found_nodes))
                            return true;
                    }
                }
            }

            found_nodes[cn] = false;
            return false;
        }

        uint32_t find_disjoint_short_cycles(node_t limit, vector<bool>& ignore) {
            uint32_t found_cycles = 0;
            vector<bool> found_nodes(ignore);
            for(node_t c_limit=2; c_limit < limit; c_limit++) {
                for(node_t n=1; n<=_size; n++) {
                    if (! _deleted[n] && ! found_nodes[n]) {
                        vector<node_t> cycle;
                        if (find_disjoint_short_cycles_rec(n, n, c_limit, found_nodes))
                            found_cycles++;
                    }
                }
            }
            return found_cycles;
        }

        uint32_t find_short_cycles(vector<vector<node_t>>& cycles, node_t limit, bool remove_subsumed) {
            uint32_t cycles_found = 0;

            vector<pair<node_t, node_t>> stack;
            stack.reserve(_size);
            vector<bool> on_stack(_size + 1);
            vector<bool> cycle_set(_size + 1);

            for(node_t n=0; n <= _size; n++) {
                if (_deleted[n])
                    continue;

                stack.emplace_back(n, limit);
                while(! stack.empty()) {
                    auto cn = stack.back().first;
                    auto cl = stack.back().second;

                    if (on_stack[cn]) {
                        on_stack[cn] = false;
                        stack.pop_back();
                    } else {
                        on_stack[cn] = true;

                        if (cl == 1) {
                            if (_succ[cn].find(n) != _succ[cn].end()) {
                                vector<node_t> cycle;
                                cycle.reserve(limit);
                                for(auto it=stack.rbegin(); it != stack.rend(); ++it) {
                                    if (on_stack[it->first] && !cycle_set[it->first]) {
                                        cycle.push_back(it->first);
                                        cycle_set[it->first] = true;
                                    }
                                }

                                bool subsumed = false;
                                if (remove_subsumed) {
                                    for (auto& cc: cycles) {
                                        // TODO: Is this always ordered?
                                        if (cc.size() >= limit)
                                            break;

                                        bool all_found = true;
                                        for(auto cc_n: cc) {
                                            if (!cycle_set[cc_n]) {
                                                all_found = false;
                                                break;
                                            }
                                        }
                                        if (all_found) {
                                            subsumed = true;
                                            break;
                                        }
                                    }
                                }
                                for(auto u : cycle)
                                    cycle_set[u] = false;

                                if (! subsumed) {
                                    assert(cycle.size() == limit);
                                    cycles.push_back(move(cycle));
                                    cycles_found++;
                                }
                            }
                        } else if (cl > 1) {
                            for(auto n2 : _succ[cn]) {
                                if (n2 > n && ! on_stack[n2])
                                    stack.emplace_back(n2, cl-1);
                            }
                        }
                    }
                }
            }

            if (VERBOSITY > 0)
                cout << limit << "-Cycles: "<< cycles_found << endl;

            return cycles_found;
        }

        /**
         * Finds a cycle starting and ending at the given start node, not using nodes in ignores.
         */
        bool find_cycle_with_node(vector<node_t>& ignores, node_t start) {
            vector<node_t> stack;
            stack.push_back(start);
            vector<bool> visited(_size + 1);

            for(auto n: ignores)
                visited[n] = true;
            if (visited[start])
                return false;

            visited[start] = true;

            while(! stack.empty()) {
                auto n = stack.back();
                stack.pop_back();

                for(auto n2: _succ[n]) {
                    if (n2 == start)
                        return true;
                    else if (! visited[n2]) {
                        visited[n2] = true;
                        stack.push_back(n2);
                    }
                }
            }
            return false;
        }

        vector<node_t> find_cycle(vector<node_t>& ignores) {
            vector<bool> ign(_size+1);
            for(auto n: ignores)
                ign[n] = true;

            return find_cycle(ign);
        }
        vector<node_t> find_cycle(const vector<bool>& ign) {
            vector<node_t> stack;
            vector<node_t> cycle;
            vector<bool> visited(_size + 1);
            vector<bool> seen(_size + 1);

            for(node_t n=1; n <= _size; n++) {
                if (! seen[n] && !visited[n] && !_deleted[n] && !ign[n]) {
                    // Start forward DFS, stack is empty
                    stack.push_back(n);

                    while(! stack.empty()) {
                        auto cn = stack.back();

                        if (seen[cn]) { // Duplicate stack entry
                            stack.pop_back();
                        } else if (visited[cn]) { // All DFS vertices have been processed, remove from stack (return)
                            visited[cn] = false;
                            seen[cn] = true;
                            stack.pop_back();
                        } else {
                            visited[cn] = true;

                            for (auto n2: _succ[cn]) {
                                if (ign[n2])
                                    continue;

                                if (visited[n2]) {
                                    // Found already visited vertex
                                    while (stack.back() != n2) {
                                        if (visited[stack.back()])
                                            cycle.push_back(stack.back());
                                        stack.pop_back();
                                    }
                                    cycle.push_back(n2);
                                    return cycle;
                                } else if (!seen[n2]) {
                                    stack.push_back(n2);
                                }
                            }
                        }
                    }
                }
            }
            return cycle;
        }



        /* Returns true if there is a path from source 's' to sink
        't' in residual graph. Also fills parent[] to store the
        path */
        bool bfs(Graph& g, map<pair<node_t, node_t>, int>& capacity, node_t s, node_t t, node_t parent[])
        {
            // Create a visited array and mark all vertices as not
            // visited
            bool visited[g.get_size() + 1];
            memset(visited, 0, sizeof(visited));
        
            // Create a queue, enqueue source vertex and mark source
            // vertex as visited
            queue<node_t> q;
            q.push(s);
            visited[s] = true;
            parent[s] = -1;
        
            // Standard BFS Loop
            while (!q.empty()) {
                node_t u = q.front();
                q.pop();
        
                for (auto v : g.get_succ(u)) {
                    auto it = capacity.find(make_pair(u,v));
                    if (!visited[v] && (it == capacity.end() || (*it).second > 0)) {
                        // If we find a connection to the sink node,
                        // then there is no point in BFS anymore We
                        // just have to set its parent and can return
                        // true
                        if (v == t) {
                            parent[v] = u;
                            return true;
                        }
                        q.push(v);
                        parent[v] = u;
                        visited[v] = true;
                    }
                }
            }
        
            // We didn't reach sink in BFS starting from source, so
            // return false
            return false;
        }
        

        vector<vector<node_t>> disjoint_cycles(node_t n) {
            Graph g(_size * 2);
            for(node_t v = 0; v <= _size; v++) {
                if(_deleted[v]) {
                    continue;
                }
                if(v != n) {
                    g.add_edge(v, v+_size);
                }
                for(auto w : _succ[v]) {
                    g.add_edge(v+_size, w);
                }
                for(auto w : _pred[v]) {
                    g.add_edge(w, v);
                }
            }
            node_t s = n + _size, t = n;
            node_t u, v;
        
            // Create a residual graph and fill the residual graph
            // with given capacities in the original graph as
            // residual capacities in residual graph
            map<pair<node_t, node_t>, int> capacity;
        
            node_t parent[g.get_size() + 1]; // This array is filled by BFS and to
                        // store path
        
            int max_flow = 0; // There is no flow initially
        
            // Augment the flow while there is path from source to
            // sink
            while (bfs(g, capacity, s, t, parent)) {
                // Find minimum residual capacity of the edges along
                // the path filled by BFS. Or we can say find the
                // maximum flow through the path found.
                int path_flow = INT_MAX;            
                for (v = t; v != s; v = parent[v]) {
                    u = parent[v];
                    auto it = capacity.find(make_pair(u,v));
                    path_flow = min(path_flow, it == capacity.end()?1:(*it).second);
                }
        
                // update residual capacities of the edges and
                // reverse edges along the path
                for (v = t; v != s; v = parent[v]) {
                    u = parent[v];
                    auto it = capacity.find(make_pair(u,v));
                    if(it == capacity.end()) {
                        capacity[make_pair(u,v)] = 1 - path_flow;
                    } else {
                        capacity[make_pair(u,v)] -= path_flow;
                    }
                    auto it2 = capacity.find(make_pair(v,u));
                    if(it2 == capacity.end()) {
                        capacity[make_pair(v,u)] = 1 + path_flow;
                    } else {
                        capacity[make_pair(v,u)] += path_flow;
                    }
                }
        
                // Add path flow to overall flow
                max_flow += path_flow;
            }
            vector<vector<node_t>> cycles;
            while(max_flow-- > 0) {
                vector<node_t> cycle;
                int parent[g.get_size() + 1];
                // Create a queue, enqueue source vertex and mark source
                // vertex as visited
                queue<node_t> q;
                q.push(s);
                parent[s] = -1;
            
                // Standard BFS Loop
                while (!q.empty()) {
                    node_t u = q.front();
                    q.pop();
            
                    for (auto v : g.get_succ(u)) {
                        auto it = capacity.find(make_pair(u,v));
                        if (it != capacity.end() && (*it).second == 0) {
                            // If we find a connection to the sink node,
                            // then there is no point in BFS anymore We
                            // just have to set its parent and can return
                            // true
                            capacity.erase(make_pair(u,v));
                            if (v == t) {
                                parent[v] = u;
                                for (node_t w = t; w != s; w = parent[w]) {
                                    if(w <= _size) {
                                        cycle.push_back(w);
                                    }
                                }
                                reverse(cycle.begin(), cycle.end());
                                cycles.push_back(cycle);
                                cycle.clear();
                            }
                            q.push(v);
                            parent[v] = u;
                        }
                    }
                }
            }
            return cycles;
        }

        bool is_acyclic(vector<node_t>& dfvs) const {
            vector<bool> set_arr(_size+1);
            for(auto n: dfvs) {
                set_arr[n] = true;
            }

            bool found = true;
            bool any_remaining;

            while (found) {
                found = false;
                any_remaining = false;
                for (node_t n=1; n <= _size; n++) {
                    if (!_deleted[n] && !set_arr[n]) {
                        any_remaining = true;
                        bool is_leaf = true;
                        for(auto n2: _succ[n]) {
                            if (! set_arr[n2]) {
                                is_leaf = false;
                                break;
                            }
                        }
                        if (is_leaf) {
                            set_arr[n] = true;
                            found = true;
                        }
                    }
                }
            }

            return !any_remaining;
        }

        void tarjan(node_t u, int32_t* disc, int32_t* low, bool* onstack, vector<uint32_t>& node_to_scc, uint32_t& foundat, uint32_t& ctr){
            static stack<node_t> st;

            disc[u]=low[u]=foundat++;
            st.push(u);
            onstack[u]=true;
            for(auto i : _succ[u]){
                if(disc[i]==-1){
                    tarjan(i, disc, low, onstack, node_to_scc, foundat, ctr);
                    low[u]=min(low[u],low[i]);
                }
                else if(onstack[i]) {
                    low[u]=min(low[u],disc[i]);
                }
            }
            if(disc[u]==low[u]){
                while(1){
                    node_t v=st.top();
                    st.pop();
                    onstack[v]=false;
                    node_to_scc[v] = ctr;
                    if(u==v)
                        break;
                }
                ctr++;
            }
        }

        vector<uint32_t> scc_idxs() {
            uint32_t ctr = 1, foundat = 1;
            vector<uint32_t> node_to_scc(_size + 1,0);
            int32_t disc[_size + 1];
            int32_t low[_size + 1];
            bool onstack[_size + 1];
            memset(disc, -1, sizeof(disc));
            memset(low, -1, sizeof(low));
            memset(onstack, 0, sizeof(onstack));
            for(node_t n = 0; n <= _size; n++) {
                if(!_deleted[n] && disc[n] == -1) {
                    tarjan(n, disc, low, onstack, node_to_scc, foundat, ctr);
                }
            }
            return node_to_scc;
        }

        void tarjan(node_t u, int32_t* disc, int32_t* low, bool* onstack, vector<vector<node_t>>& sccs, uint32_t& foundat){
            static stack<node_t> st;

            disc[u]=low[u]=foundat++;
            st.push(u);
            onstack[u]=true;
            for(auto i : _succ[u]){
                if(disc[i]==-1){
                    tarjan(i, disc, low, onstack, sccs, foundat);
                    low[u]=min(low[u],low[i]);
                }
                else if(onstack[i]) {
                    low[u]=min(low[u],disc[i]);
                }
            }
            if(disc[u]==low[u]){
                vector<node_t> scctem;
                while(1){
                    node_t v = st.top();
                    st.pop();
                    onstack[v] = false;
                    scctem.push_back(v);
                    if(u==v)
                        break;
                }
                sccs.push_back(scctem);
            }
        }

        vector<vector<node_t>> sccs() {
            uint32_t foundat = 1;
            vector<vector<node_t>> sccs;
            int32_t disc[_size + 1];
            int32_t low[_size + 1];
            bool onstack[_size + 1];
            memset(disc, -1, sizeof(disc));
            memset(low, -1, sizeof(low));
            memset(onstack, 0, sizeof(onstack));
            for(node_t n = 0; n <= _size; n++) {
                if(!_deleted[n] && disc[n] == -1) {
                    tarjan(n, disc, low, onstack, sccs, foundat);
                }
            }
            return sccs;
        }

        bool find_separated_components_rec_call(vector<bool>& on_stack, vector<node_t>& stack, node_t cn, vector < vector < node_t>>& cycles, vector<vector<size_t>>& node_to_cycle) {
            on_stack[cn] = true;
            stack.push_back(cn);
            for(auto n: _succ[cn]) {
                if(! on_stack[n]) {
                    if (find_separated_components_rec_call(on_stack, stack, n, cycles, node_to_cycle))
                        return true;
                } else {
                    unordered_set<size_t> c_cycles;
                    vector<bool> c_cycle(_size+1);

                    for(auto it=stack.rbegin(); true; ++it) {
                        c_cycle[*it] = true;
                        c_cycles.insert(node_to_cycle[*it].begin(), node_to_cycle[*it].end());
                        if(*it == n)
                            break;
                    }
                    for(auto idx : c_cycles) {
                        bool all_found = true;
                        for(auto n2 : cycles[idx]) {
                            if (!c_cycle[n2]) {
                                all_found = false;
                                break;
                            }
                        }
                        if (all_found)
                            return true;
                    }
                    return false;
                }
            }
            on_stack[cn] = false;
            stack.pop_back();
            return false;
        }

        bool find_separated_components_rec(vector<vector<node_t>>& cycles, bool stop_immediately) {
            vector<node_t> stack;
            vector<bool> on_stack(_size+1);
            vector<vector<size_t>> node_to_cycle(_size+1);

            for(auto i=0; i < cycles.size(); i++) {
                for(auto n: cycles[i]) {
                    node_to_cycle[n].push_back(i);
                }
            }

            for(node_t n=1; n <= _size; n++) {
                if (!_deleted[n]) {
                    if (find_separated_components_rec_call(on_stack, stack, n, cycles, node_to_cycle))
                        return true;
                }
            }

            return false;
        }

        vector<node_t> find_non_subsumed_cycle(vector<vector<node_t>>& cycles) {
            vector<bool> dont_mark(_size+1);
            vector<node_t> cycle;

            vector<node_t> stack;
            vector<bool> visited(_size + 1);
            vector<bool> seen(_size + 1);
            vector<vector<size_t>> node_to_cycle(_size+1);
            vector<vector<bool>> cycles_set(cycles.size(), vector<bool>(_size+1));
            unordered_set<size_t> used_cycles;
            vector<bool> cycle_set(_size+1);

            for(size_t i=0; i < cycles.size(); i++) {
                for(auto n: cycles[i]) {
                    cycles_set[i][n] = true;
                    node_to_cycle[n].push_back(i);
                }
            }

            for(node_t n=1; n <= _size; n++) {
                assert(! visited[n]);
                if (! seen[n] && !visited[n] && !_deleted[n]) {
                    vector<vector<node_t>> c_component;
                    // Start forward DFS, stack is empty
                    stack.emplace_back(n);

                    while(! stack.empty()) {
                        auto cn = stack.back();

                        if (seen[cn]) { // Duplicate stack entry
                            stack.pop_back();
                        } else if (visited[cn]) { // All DFS vertices have been processed, remove from stack (return in recursive variant)
                            visited[cn] = false;
                            if (dont_mark[cn])
                                dont_mark[cn] = false;
                            else
                                seen[cn] = true;
                            stack.pop_back();
                        } else {
                            visited[cn] = true;
                            // Copy as the pushes on the stack may invalidate the memory
                            for (auto n2: _succ[cn]) {
                                if (seen[n2])
                                    continue;

                                std::fill(cycle_set.begin(), cycle_set.end(), false);

                                if (visited[n2]) {
                                    // Found already visited vertex -> extract cycle
                                    used_cycles.clear();
                                    for (auto it = stack.rbegin(); true; ++it) {
                                        if (visited[*it]) {
                                            cycle.push_back(*it);
                                            cycle_set[*it] = true;
                                            used_cycles.insert(node_to_cycle[*it].begin(), node_to_cycle[*it].end());
                                        }
                                        if (*it == n2)
                                            break;
                                    }

                                    bool is_subsumed = false;
                                    for(auto idx : used_cycles) {
                                        bool all_found = true;
                                        for(auto u : cycles[idx]) {
                                            if (! cycle_set[u]) {
                                                all_found = false;
                                                break;
                                            }
                                        }
                                        if (all_found) {
                                            for(auto u : cycles[idx]) {
                                                if (! cycle_set[u]) {
                                                    dont_mark[u] = true;
                                                }
                                            }
                                            is_subsumed = true;
                                        }
                                    }

                                    if (! is_subsumed) {
                                        return cycle;
                                    }
                                    cycle.clear();
                                } else {
                                    stack.emplace_back(n2);
                                }
                            }
                        }
                    }
                    seen[n] = true;
                }
            }

            cycle.clear();
            return cycle;
        }

        bool find_elementary_cycle_with_edge(node_t u, node_t v, vector<vector<bool>>& markers) {
            vector<node_t> stack;
            stack.push_back(v);
            vector<bool> on_stack(_size + 1);

            while(! stack.empty()) {
                auto n = stack.back();

                if (on_stack[n]) {
                    on_stack[n] = false;
                    stack.pop_back();
                } else {
                    on_stack[n] = true;

                    bool has_cycle = false;
                    for (auto n2: _succ[n]) {
                        if (n2 == u || on_stack[n2]) {
                            has_cycle = true;
                            node_t prev = n2;
                            for(auto it=stack.rbegin(); it != stack.rend() && *it != n2; ++it) {
                                if (on_stack[*it]) {
                                    markers[*it][prev] = true;
                                }
                            }
                            if (n2 == u) {
                                markers[u][v] = true;
                                return true;
                            }
                        }
                    }

                    if (! has_cycle) {
                        stack.insert(stack.end(), _succ[n].begin(), _succ[n].end());
                    }
                }
            }
            return false;
        }
    private:
        vector<unordered_set<node_t>> _succ;
        vector<unordered_set<node_t>> _pred;
        node_t _size;
        vector<bool> _deleted;
    };

    // Function to return the next random number
    node_t getNum(vector<node_t>& v)
    {
    
        // Size of the vector
        node_t n = v.size();
    
        
    
        // Make sure the number is within
        // the index range
        node_t index = rand() % n;
    
        // Get random number from the vector
        node_t num = v[index];
    
        // Remove the number from the vector
        swap(v[index], v[n - 1]);
        v.pop_back();
    
        // Return the removed number
        return num;
    }
    
    // Function to generate n non-repeating random numbers
    vector<node_t> generateRandom(node_t n)
    {
        // Generate a random number
        auto t = time(NULL);
        cout << t << endl;
        srand(t);
        vector<node_t> v(n);
    
        // Fill the vector with the values
        // 1, 2, 3, ..., n
        for (node_t i = 0; i < n; i++)
            v[i] = i+1;
    
        // While vector has elements
        // get a random number from the vector and print it


        vector<node_t> ret(1,0);
        while (v.size()) {
            ret.push_back(getNum(v));
        }
        return ret;
    }

    Graph parse() {
        node_t cnt = 0;
        node_t vertices = INVALID_NODE;

        for (std::string ln; std::getline(std::cin, ln);) {
            if (ln[0] == '%')
                continue;

            ln.erase(ln.begin(), std::find_if(ln.begin(), ln.end(),
                                              std::not1(std::ptr_fun<int, int>(std::isspace))));
            istringstream iss(ln);
            string tok;

            for (long i = 0; getline(iss, tok, ' '); i++) {
                tok.erase(tok.begin(), std::find_if(tok.begin(), tok.end(),
                                                    std::not1(std::ptr_fun<int, int>(std::isspace))));
                vertices = stol(tok);
                break;
            }
            ++cnt;
            break;
        }

        Graph g(vertices);
        //vector<node_t> permutation = generateRandom(vertices);
        for (std::string ln; std::getline(std::cin, ln);) {
            if (ln[0] == '%')
                continue;

            if (ln.length() > 0) {
                // Trim
                ln.erase(ln.begin(), std::find_if(ln.begin(), ln.end(),
                                                  std::not1(std::ptr_fun<int, int>(std::isspace))));
                istringstream iss(ln);
                string tok;

                for (long i = 0; getline(iss, tok, ' '); i++) {
                    tok.erase(tok.begin(), std::find_if(tok.begin(), tok.end(),
                                                        std::not1(std::ptr_fun<int, int>(std::isspace))));
                    //g.add_edge(permutation[cnt], permutation[stol(tok)]);
                    g.add_edge(cnt, stol(tok));
                }
            }
            ++cnt;
        }

        return g;
    }

    class VcGraph {
    public:
        explicit VcGraph(node_t size) : _adjacency(size+1), _longCycleEdges(size + 1) {

        }
        void add_edge(node_t u, node_t v, bool is_special=false) {
            if (is_special) {
                auto it = _longCycleEdges[u].find(v);
                if (it == _longCycleEdges[u].end()) {
                    assert(! adjacent(u, v));
                    _longCycleEdges[u].emplace(v, 1);
                    _longCycleEdges[v].emplace(u, 1);
                } else {
                    _longCycleEdges[u][v]++;
                    _longCycleEdges[v][u]++;
                }
            } else {
                assert(_longCycleEdges[u].find(v) == _longCycleEdges[u].end() || !adjacent(u, v));
            }

            _adjacency[u].insert(v);
            _adjacency[v].insert(u);
        }

        void remove_edge(node_t u, node_t v) {
            _adjacency[u].erase(v);
            _adjacency[v].erase(u);
        }

        void remove_vertex(node_t u) {
            for(auto v : _adjacency[u]) {
                if (u != v)
                    _adjacency[v].erase(u);
            }
            _adjacency[u].clear();
        }

        void transfer_edges(node_t u, node_t v) {
            for(auto w: _adjacency[u]) {
                if (w != v) {
                    add_edge(v, w);
                }
            }
        }

        bool check_long_cycle(node_t u, node_t v, bool decrement=true) {
            auto it = _longCycleEdges[u].find(v);
            if (it == _longCycleEdges[u].end())
                return false;
            if (decrement) {
                it->second--;
                assert(_longCycleEdges[u][v] + 1 == _longCycleEdges[v][u]);
                if (--_longCycleEdges[v][u] == 0) {
                    _longCycleEdges[v].erase(u);
                    _longCycleEdges[u].erase(v);
                    return false;
                }
            } else {
                return _longCycleEdges[v][u] > 0;
            }
            return true;
        }

        set<node_t>& get_adjacency(node_t u) {
            return _adjacency[u];
        }

        [[nodiscard]] bool is_deleted(node_t u) const {
            return _adjacency[u].empty();
        }

        [[nodiscard]] node_t degree (node_t u) const {
            return _adjacency[u].size();
        }

        node_t count_long (node_t u, node_t v) const {
            auto it = _longCycleEdges[u].find(v);
            if (it == _longCycleEdges[u].end())
                return 0;
            return it->second;
        }

        bool adjacent(node_t u, node_t v){
            return _adjacency[u].find(v) != _adjacency[u].end();
        }
    private:
        vector<set<node_t>> _adjacency;
        vector<unordered_map<node_t, size_t>> _longCycleEdges;
    };
}
#endif //CPP_GRAPH_H
