import subprocess
import tempfile
import os
import inspect
import time

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '../external'))

class VertexCover(object):
    nr_vertices = 0
    edges = []
    
    def __init__(self, nr_vertices):
        self.nr_vertices = nr_vertices
    
    def solve_maxsat(self):
        cnf_fd, cnf_tmp = tempfile.mkstemp()
        top = self.nr_vertices + 1
        with os.fdopen(cnf_fd, mode='wb') as cnf_out:
            cnf_out.write(f"p wcnf {self.nr_vertices} {len(self.edges) + self.nr_vertices} {top}\n".encode())
            for e in self.edges:
                cnf_out.write(f"{top} {-e[0]} {-e[1]} 0\n".encode())
            for v in range(1, self.nr_vertices + 1):
                cnf_out.write(f"1 {v} 0\n".encode())
        
        start = time.time()
        p = subprocess.Popen([ os.path.join(src_path, "EvalMaxSAT/build/EvalMaxSAT_bin"), cnf_tmp, "--timeout_fast", "1"], stdout=subprocess.PIPE, close_fds = True)#, stderr=subprocess.PIPE)
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
                solution = [ -int(i) for i in line[2:-1].split() if int(i) < 0 ]
            elif line[0] == 'o':
                weight = int(line[2:-1])
        if solution is None:
            raise Exception("MaxSAT solver did not print an assignment!")
        print(f"Solving time:         {time.time() - start}")
        #os.remove(cnf_tmp)
        return (weight, solution)
    
    def solve_heuristic(self):
        cnf_fd, cnf_tmp = tempfile.mkstemp()
        print(cnf_tmp)
        with os.fdopen(cnf_fd, mode='wb') as cnf_out:
            cnf_out.write(f"p vc {self.nr_vertices} {len(self.edges)}\n".encode())
            for e in self.edges:
                cnf_out.write(f"e {e[0]} {e[1]}\n".encode())
        
        start = time.time()
        p = subprocess.Popen([ os.path.join(src_path, "FastVCv2015.11/fastvc"), cnf_tmp, "1341234", "1"], stdout=subprocess.PIPE, close_fds = True)#, stderr=subprocess.PIPE)
        p.wait()
        solution = None
        for line in p.stdout.readlines():
            line = line.decode()
            if len(line) == 0:
                continue
            if line.startswith("c"):
                continue
            
            solution = [ int(i) for i in line.split() if int(i) ]
            weight = len(solution)
            break
        if solution is None:
            raise Exception("Solver did not print an assignment!")
        #os.remove(cnf_tmp)
        return (weight, solution)
    
def from_ordered_graph(ordering, graph):
    idx_order = {x: i for (i, x) in enumerate(ordering)}
    ret = VertexCover(max(ordering))
    ret.edges = [ (v,w) for v,w in graph.edges if idx_order[v] > idx_order[w] ]
    return ret
    