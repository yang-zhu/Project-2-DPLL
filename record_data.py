import os
import subprocess
from collections import defaultdict
import time
import json
import argparse

# Store the solving time of every configuration in stats_dict.
def record_data(configs, files, solver, timeout):  
    stats_dict = defaultdict(list)
    for conf in configs:
        # Print the current progress on the console.
        print("\n"+conf)
        print("==============")
        for i, f in enumerate(files):
            print(f'solving {i+1}/{len(files)}: {os.path.basename(f)}')
            start = time.time()
            try:
                subprocess.run([solver, *configs[conf], f], stdout=subprocess.DEVNULL, timeout = timeout)
                end = time.time()
                print("%.4fs" % (end-start))
                stats_dict[conf].append(end-start)
            except subprocess.TimeoutExpired:
                print("timeout")
    return stats_dict
        
        
if __name__ == '__main__':
    configs = {
    "none":[], 
    "purelit":['-p'], 
    'SLIS':['-slis'], 
    'SLIS + purelit':['-slis', '-p'], 
    'SLCS':['-slcs'], 
    'SLCS + purelit':['-slcs', '-p'], 
    'DLIS':['-dlis'], 
    'DLIS + purelit':['-dlis', '-p'], 
    'DLCS':['-dlcs'], 
    'DLCS + purelit':['-dlcs', '-p'], 
    'backtrack count':['-bc'], 
    'backtrack count + purelit':['-bc', '-p'], 
    'MOM':['-mom'], 
    'MOM + purelit':['-mom', '-p'], 
    'Boehm':['-boehm'], 
    'Boehm + purelit':['-boehm', '-p'], 
    'Jeroslow-Wang':['-jw'],
    'Jeroslow-Wang + purelit':['-jw', '-p']
    }

    parser = argparse.ArgumentParser(description="Records solver runtime.")
    parser.add_argument('solver', help='path to DPLL solver')
    parser.add_argument('timeout', help='timeout for each formula', type=int)
    parser.add_argument('write_to', help='the file to write results to')
    parser.add_argument('benchmarks', help='benchmarks to be tested', nargs='+')
    args = parser.parse_args()

    # Only create a new file when the given file does not exist yet.
    if not os.path.isfile(args.write_to): 
        with open(args.write_to, 'w') as f:
            f.write(json.dumps(record_data(configs, args.benchmarks, args.solver, args.timeout)))
    else:
        print(args.write_to, "already exists.")