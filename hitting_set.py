import subprocess
import tempfile
import os
import inspect
import time

import tools
from tools import find_short_cycles, find_cycles_length

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '../external'))

class HittingSet(object):
    nr_vertices = 0
    sets = []
    
    def __init__(self, nr_vertices):
        self.nr_vertices = nr_vertices
    
    def solve_maxsat(self):
        cnf_fd, cnf_tmp = tempfile.mkstemp()
        top = self.nr_vertices + 1
        with os.fdopen(cnf_fd, mode='wb') as cnf_out:
            cnf_out.write(f"p wcnf {self.nr_vertices} {len(self.sets) + self.nr_vertices} {top}\n".encode())
            for c in self.sets:
                cnf_out.write(f"{top} {' '.join([ str(-v) for v in c ])} 0\n".encode())
            for v in range(1, self.nr_vertices + 1):
                cnf_out.write(f"1 {v} 0\n".encode())
        
        start = time.time()
        p = subprocess.Popen([ os.path.join(src_path, "EvalMaxSAT/build/EvalMaxSAT_bin"), cnf_tmp], stdout=subprocess.PIPE, close_fds = True)#, stderr=subprocess.PIPE)
        solution = None
        while p.poll() is None or solution is None:
            line = p.stdout.readline().decode()
            if len(line) == 0:
                continue
            if line.startswith("s"):
                if line[2:] == "OPTIMUM FOUND":
                    continue
                elif line[2:] == "UNKNOWN":
                    raise Exception("MaxSAT solver returned UNKNOWN")
                elif line[2:] == "SATISFIABLE":
                    raise Exception("MaxSAT solver returned SATISFIABLE. Probably it was interrupted during execution")
                elif line[2:] == "UNSATISFIABLE":
                    weight = top
                    solution = list(range(1,self.nr_vertices + 1))
            elif line[0] == 'v':
                solution = [ int(i) for i in line[2:-1].split() ]
            elif line[0] == 'o':
                weight = int(line[2:-1])
        if solution is None:
            raise Exception("MaxSAT solver did not print an assignment!")
        print(f"Solving time:         {time.time() - start}")
        #os.remove(cnf_tmp)
        return (weight, solution)
    
def from_graph(graph, verbose = False):
    ret = HittingSet(max(graph.nodes))
    ret.sets = find_short_cycles(graph, verbose=verbose)
    return ret
    