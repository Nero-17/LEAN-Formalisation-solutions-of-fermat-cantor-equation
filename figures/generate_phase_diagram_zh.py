"""Phase diagram with exact values and numerical transition estimates.

Run with Python and matplotlib. The upper shaded region is guaranteed by the
uniform real-exponent bound; it does not assert an exact transition location.
Squares read finite-depth estimates from the accompanying CSV files;
circles retain the previously proved exact values. See the method notes.
"""
from pathlib import Path
from fractions import Fraction
import math
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

OUT = Path(__file__).resolve().parent
with (OUT/'phase-transition-estimates.csv').open(newline='',encoding='utf-8') as f:
    estimates = {Fraction(row['n']):float(row['estimate']) for row in csv.DictReader(f)}
with (OUT/'first-transition-estimates.csv').open(newline='',encoding='utf-8') as f:
    first_estimates = {Fraction(row['n']):row for row in csv.DictReader(f)}
plt.rcParams.update({'font.family': ['Microsoft YaHei', 'STIXGeneral'], 'font.size': 12,
                     'mathtext.fontset': 'stix', 'pdf.fonttype': 42})

blue = ['#155AA4', '#8BB9E5', '#DAEAF9']
red = ['#B73F50', '#E5A6AE', '#F3DDE1']
fig, ax = plt.subplots(figsize=(12, 7.4))
fig.subplots_adjust(left=.075, right=.975, bottom=.22, top=.97)
ax.axhspan(0, .25, color='#F1F5F9', zorder=0)
ax.axhspan((math.sqrt(3)-1)/2, .5, color='#F8DFE3', zorder=1)
ax.set_axisbelow(True)
ax.grid(axis='y', color='#E7EBF0', lw=.65)
ax.axhline(.25, color=blue[2], lw=4.5, zorder=3)
ax.axhline(1/3, color='#FF0000', lw=2.5, zorder=4)
ax.axhline((math.sqrt(3)-1)/2, color=red[2], lw=3.5,
           ls=(0,(4,3)), zorder=3)

fractions = sorted({Fraction(a,b) for b in range(1,4)
                    for a in range(2*b,8*b+1)},
                   key=lambda f: f.denominator, reverse=True)
for frac in fractions:
    n = float(frac)
    kind = 0 if frac.denominator == 1 else 1
    ax.plot(n, estimates[frac], marker='s', linestyle='none',
            ms=6.2 if kind == 0 else 4.8, color=red[kind],
            markeredgecolor='white', markeredgewidth=.35,
            zorder=10, clip_on=False)
for frac in fractions:
    n = float(frac)
    kind = 0 if frac.denominator == 1 else 1
    value = float(first_estimates[frac]['estimate'])
    assert .25 <= value <= .5
    if first_estimates[frac]['kind'] == 'exact':
        ax.plot(n, value, 'o', ms=6, color=blue[kind], zorder=11, clip_on=False)
    else:
        ax.plot(n, value, marker='s', linestyle='none',
                ms=6.2 if kind == 0 else 4.8, color=blue[kind],
                markeredgecolor='white', markeredgewidth=.35,
                zorder=11, clip_on=False)


ax.text(5, .12, r'$\dim_{\mathrm{H}}(E_{n,\lambda})=0$  (定理 3.2)',
        ha='center', va='center', fontsize=22, color='#556676')
ax.text(5, .45, r'$\dim_{\mathrm{H}}(E_{n,\lambda})>0$',
        ha='center', va='center', fontsize=22, color='#A34254', zorder=12)
ax.text(5.2, .378,
        r'所有实数 $n>1$: $\lambda_{\max}(n)<(\sqrt{3}-1)/2$  (定理 4.2)',
        ha='center', fontsize=17, color='#AF7E87',
        bbox=dict(facecolor='white', edgecolor='none', alpha=.94, pad=3), zorder=10)
ax.text(5.8, .226,
        r'无理指数 $n$: $\lambda_{\min}(n)=1/4$  (定理 3.7)',
        ha='center', color='#769DC3', fontsize=17, zorder=10)
ax.annotate(r'$2-\sqrt{3}$  (定理 4.4)',
            xy=(2,2-math.sqrt(3)), xytext=(2.10,.307),
            color=blue[0], fontsize=12,
            arrowprops=dict(arrowstyle='-',color=blue[0],lw=.8), zorder=10)
ax.annotate(r'$\lambda_{\min}(4)=1/4$  (命题 3.10)',
            xy=(4,.25), xytext=(3.10,.196),
            color=blue[0], fontsize=11.5,
            arrowprops=dict(arrowstyle='-',color=blue[0],lw=.8,
                            connectionstyle='arc3,rad=-.12'), zorder=10)
ax.text(5.2, .326, r'所有实数 $n>1$: $\dim_{\mathrm{H}}(E_{n,1/3})>0$  (定理 3.1)',
        ha='center', va='top', fontsize=15.5, color='#FF0000',
        bbox=dict(facecolor='white',edgecolor='none',alpha=.94,pad=2), zorder=12)
ax.plot(2, 1/3, marker='*', linestyle='none', markersize=17,
        color='#FF0000', markeredgecolor='white', markeredgewidth=.7,
        zorder=20, clip_on=False)
ax.set_xlim(2,8)
ax.set_ylim(0,.5)
ax.set_xticks(range(2,9))
ax.set_xlabel(r'$n$', fontsize=17, labelpad=6)
ax.set_ylabel(r'$\lambda$', fontsize=19, rotation=0, labelpad=20)
ax.set_yticks([0,.1,.2,.25,1/3,.4,.5])
ax.set_yticklabels(['0','0.1','0.2',r'$\frac{1}{4}$',r'$\frac{1}{3}$','0.4',r'$\frac{1}{2}$'])
ax.tick_params(length=4, color='#ADB5BF', labelsize=12, pad=6)
for spine in ax.spines.values():
    spine.set_color('#ABB4BF')
    spine.set_linewidth(.8)

handles = [Line2D([],[],color=blue[i],marker='s',linestyle='none',ms=6,label='首次：'+name)
           for i,name in enumerate(['整数','非整数有理数'])]
handles += [Line2D([],[],color=blue[2],lw=3,label='首次：无理数')]
handles += [Line2D([],[],color=red[i],marker='s',linestyle='none',ms=6,
                   label='末次：'+name)
            for i,name in enumerate(['整数','非整数有理数'])]
handles += [Line2D([],[],color=red[2],lw=3,ls='--',label='末次上界：所有实数')]
# Matplotlib lays out legends by columns: pair first/last for each class.
handles = [handles[j] for j in [0,3,1,4,2,5]]
fig.legend(handles=handles,ncol=3,loc='lower center',bbox_to_anchor=(.52,.055),
           frameon=False,columnspacing=1.8,handlelength=1.8,fontsize=12)
fig.text(.52,.017,'圆点：精确值     |     方块：数值估计，非严格界',
         ha='center',fontsize=11.5,color='#586577')
fig.savefig(OUT/'phase-diagram-zh.pdf', facecolor='white')
fig.savefig(OUT/'phase-diagram-zh.svg', facecolor='white')
fig.savefig(OUT/'phase-diagram-zh-preview.png', dpi=220, facecolor='white')
print('Saved diagram with verified manuscript theorem references.')
