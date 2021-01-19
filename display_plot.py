from collections import defaultdict
import sys
import json
import seaborn as sns
import matplotlib.pyplot as plt

# Combine the stats from several files.
stats_combined = defaultdict(list)
files = sys.argv[1:]
for file in files:
    with open(file, 'r') as f:
        stats_part = json.loads(f.read())
        for conf in stats_part:
            stats_combined[conf] += stats_part[conf]

# Convert the structure of stats_combined for seaborn.
stats_dict = defaultdict(list)
for conf in stats_combined:
    runtimes = sorted(stats_combined[conf])
    for i, runtime in enumerate(runtimes):
        stats_dict['Configuration'].append(conf)
        stats_dict['Instances'].append(i+1)
        stats_dict['Time'].append(runtime)

# Display the cactus plot.
fig, axs = plt.subplots(ncols=1)
fig.canvas.set_window_title('Evaluation')
markers = (['o', 'v']*len(stats_combined))[:len(stats_combined)]
colors = [color for color in sns.color_palette('bright') for _ in range(2)][:len(stats_combined)]
sns.lineplot(x='Instances', y='Time', hue='Configuration', data=stats_dict, markers=markers, style="Configuration", dashes=False, palette=colors)
axs.set(xlabel = 'number of solved instances', ylabel = 'CPU time (s)')
plt.show()