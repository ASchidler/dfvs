import sys
import os

base_path = "/home1/aschidler"

pattern1 = sys.argv[1]
pattern2 = sys.argv[2]

results1 = {}
results2 = {}

for cf in os.listdir(base_path):
    if cf.startswith(pattern1) or cf.startswith(pattern2):
        with open(os.path.join(base_path, cf)) as inp:
            for cl in inp:
                if cl.startswith("Found DFVS"):
                    result = int(cl.split(" ")[2])
                    instance = cf.split(".")[-1]
                    if cf.startswith(pattern1):
                        results1[instance] = result
                    else:
                        results2[instance] = result
                    break

for k, v in results1.items():
    if k in results2:
        if v != results2[k]:
            print(f"Mismatch in instance k {v}/{results2[k]}")

print(f"Checked {len(results1)}/{len(results2)} Results")
