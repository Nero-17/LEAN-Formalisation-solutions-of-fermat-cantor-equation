"""Shared numerical magnifier for the English and Chinese phase diagrams."""
from pathlib import Path
import csv
import numpy as np
from matplotlib.patches import Ellipse, ConnectionPatch


def add_circle_zoom(ax, chinese=False):
    with (Path(__file__).parent/'circle-zoom.csv').open(encoding='utf-8') as f:
        rows = list(csv.DictReader(f))
    assert not any(int(row['capped']) for row in rows)
    parameters = np.array([float(row['lambda']) for row in rows])
    dimensions = np.array([float(row['dimension_48']) for row in rows])
    extinct = np.array([bool(int(row['all_extinct'])) for row in rows])
    inset = ax.inset_axes([.065, .075, .44, .285], zorder=30)
    inset.set_facecolor('#FFFFFF')
    inset.plot(parameters, dimensions, color='#B73F50', lw=.85, zorder=3)
    inset.fill_between(parameters, dimensions, color='#E5A6AE', alpha=.22, zorder=2)
    inset.scatter(parameters[extinct], np.zeros(extinct.sum()), s=9,
                  color='#155AA4', linewidths=0, zorder=4)
    inset.set_xlim(parameters[0], parameters[-1])
    inset.set_ylim(-.008, .16)
    inset.set_xticks([.268, .272, .276])
    inset.set_xticklabels(['0.268', '0.272', '0.276'])
    inset.set_yticks([0, .05, .10])
    inset.set_yticklabels(['0', '0.05', '0.10'])
    inset.tick_params(labelsize=9, length=3, pad=2, colors='#526170')
    inset.grid(axis='y', lw=.45, color='#E8ECF0', zorder=0)
    inset.set_xlabel(r'$\lambda$', fontsize=12, labelpad=-1)
    inset.set_ylabel(r'$\widehat d_{48}$', fontsize=12, rotation=0, labelpad=15)
    inset.text(.025, .92, r'$\alpha=2$  '+('有限层数值估计' if chinese else 'finite-depth estimate'),
               transform=inset.transAxes, fontsize=10.5, color='#526170', va='top',
               bbox=dict(facecolor='white', edgecolor='none', alpha=.93, pad=1))
    for spine in inset.spines.values():
        spine.set_color('#8A97A5')
        spine.set_linewidth(.9)
    lens = Ellipse((2, .2721), width=.20, height=.016,
                   facecolor='none', edgecolor='#788897', lw=1.2,
                   zorder=25, clip_on=False)
    ax.add_patch(lens)
    connector = ConnectionPatch(xyA=(2.065, .2660), coordsA=ax.transData,
                                xyB=(0, 1), coordsB=inset.transAxes,
                                color='#8A97A5', lw=1.05, zorder=24,
                                clip_on=False)
    ax.add_artist(connector)
    return inset
