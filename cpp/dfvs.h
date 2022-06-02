//
// Created by aschidler on 5/10/22.
//

#ifndef VERBOSITY
#define VERBOSITY 1
#endif

#ifndef CPP_DFVS_H
#define CPP_DFVS_H
#include <cctype>
#include <stdint-gcc.h>
#include <cassert>

typedef uint32_t node_t;
#define INVALID_NODE UINT32_MAX

namespace dfvs {
    struct binary_reduced {
        node_t n;
        node_t a;
        node_t b;
        node_t c;
        node_t d;
        bool is_rule6or7 = false;
        bool is_empty_case = false;
        bool is_rule8 = false;
        std::vector<std::pair<node_t, node_t>> edges;
    };
}

#endif //CPP_DFVS_H
