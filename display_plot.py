from collections import defaultdict
import sys
import json
import seaborn as sns
import matplotlib.pyplot as plt

stats = defaultdict(list)
files = sys.argv[1:]
for file in files:
    with open(file, 'r') as f:
        stats_part = json.loads(f.read())
        for conf in stats_part:
            stats[conf] += stats_part[conf]

stats_dict = defaultdict(list)
for conf in stats:
    runtimes = sorted(stats[conf])
    for i, runtime in enumerate(runtimes):
        stats_dict['Configuration'].append(conf)
        stats_dict['Instances'].append(i+1)
        stats_dict['Time'].append(runtime)


fig, axs = plt.subplots(ncols=1)
fig.canvas.set_window_title('Evaluation')
sns.lineplot(x='Instances', y='Time', hue='Configuration', data=stats_dict, markers=['o']*len(stats), style="Configuration", dashes=False)
axs.set(xlabel = 'number of solved instances', ylabel = 'CPU time (s)')
plt.show()