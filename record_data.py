import os
import subprocess
import sys
from collections import defaultdict
import time
import json

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
    solver = sys.argv[1]    
    timeout = int(sys.argv[2])
    write_to = sys.argv[3]
    files = sys.argv[4:]

    # Only create a new file when the given file does not exist in the current directory yet.
    if not os.path.isfile(write_to): 
        with open(write_to, 'w') as f:
            f.write(json.dumps(record_data(configs, files, solver, timeout)))
    else:
        print(write_to, "already exists.")