# Dagger

## Introduction

Dagger is a Directed Feedback Fertex Set solver written in C++.
The solver first uses extensive preprocessing to reduce the size of the instance.
Afterwards a modified version of EvalMaxSAT is used to compute the optimal DFVS.
EvalMaxSAT is instantiated with 
- A set of clauses corresponding to a limited number of cycles that must be broken.
- The digraph that remains after preprocessing.
During solving, the modified version of glucose dynamically detects cycles by maintaining a topological order of the vertices of the digraph that are included in the current partial solution.
If the digraph induced by the current partial solution has a cycle a clause capturing this cycle is learnt and a conflict is produced.

## Dependencies

Dependencies already included:
- EvalMaxSAT : https://github.com/FlorentAvellaneda/EvalMaxSAT
- glucose : https://www.labri.fr/perso/lsimon/glucose/
- CLI11 : https://github.com/CLIUtils/CLI11

## Installation

```bash
git clone TODO
cmake .
make
```

## Usage

```bash
cat <digraph file> | ./dagger
```

## Solver Description

TODO

