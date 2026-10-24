"""Finite-depth, 60-digit local cylinder counts for the alpha=2 inset.

The reported slopes are numerical growth proxies, not Hausdorff dimensions.
No search outcome is replaced by the analytic zero/positive classification.
"""
from decimal import Decimal, localcontext
from pathlib import Path
import argparse
import csv
import json
import math
import time
import numpy as np
from scan_last_transition import candidate_m


def local_counts(lam, k, m, depth, cap):
    one = Decimal(1)
    scale = lam ** m
    ratio = lam ** (m - 2*k)
    points = [(Decimal(0), Decimal(0))]
    width = one
    counts = []

    def residual(s, t):
        x = one - lam + lam*s
        y = one - lam + lam*t
        return x*x - ratio*y*(2-scale*y)

    for level in range(depth+1):
        points = [(s, t) for s, t in points
                  if residual(s, t+width) <= 0 <= residual(s+width, t)
                  and lam**k*(one-lam+lam*s)+scale*(one-lam+lam*t) <= one]
        counts.append(len(points))
        if not points or len(points) >= cap or level == depth:
            break
        shift = (one-lam)*width
        points = [(s+ds, t+dt) for s, t in points
                  for ds, dt in [(0, 0), (0, shift), (shift, 0), (shift, shift)]]
        width *= lam
    return {'k': k, 'm': m, 'counts': counts, 'capped': counts[-1] >= cap}


def slope(counts, depth, lam):
    if len(counts) <= depth or counts[depth] == 0:
        return 0.0
    start = depth-10
    if not all(counts[start:depth+1]):
        return 0.0
    return max(0.0, float(np.polyfit(np.arange(start, depth+1),
                       np.log(counts[start:depth+1]), 1)[0])/math.log(1/float(lam)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--samples', type=int, default=361)
    parser.add_argument('--depth', type=int, default=48)
    parser.add_argument('--kmax', type=int, default=12)
    parser.add_argument('--cap', type=int, default=20000)
    parser.add_argument('--output', default='circle-zoom')
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    rows = []
    start = time.time()
    with localcontext() as context:
        context.prec = 60
        for i in range(args.samples):
            lam = Decimal('0.2679') + Decimal('0.009')*i/(args.samples-1)
            records = []
            for k in range(args.kmax+1):
                for m in candidate_m(2, float(lam), k):
                    records.append(local_counts(lam, k, m, args.depth, args.cap))
            eligible = [r for r in records if not r['capped']]
            estimates = {str(d): max((slope(r['counts'], d, lam) for r in eligible), default=0.0)
                         for d in [args.depth-12, args.depth]}
            dimensions = {str(d): max((math.log(max(r['counts'][d], 1))/(d*math.log(1/float(lam)))
                          for r in eligible if len(r['counts']) > d), default=0.0)
                          for d in [args.depth-12, args.depth]}
            rows.append({'lambda': str(lam), 'estimates': estimates,
                         'dimension_proxies': dimensions,
                         'all_extinct': all(r['counts'][-1] == 0 for r in records),
                         'capped': any(r['capped'] for r in records), 'sources': records})
            if i % 30 == 0:
                print(i, str(lam)[:10], estimates, round(time.time()-start, 1), flush=True)
    payload = {'alpha': 2, 'precision_digits': 60, 'depth': args.depth,
               'kmax': args.kmax, 'cap': args.cap, 'samples': args.samples,
               'regression_levels': 11, 'seconds': time.time()-start,
               'status': 'finite-depth numerical growth proxy, not a rigorous dimension estimate',
               'rows': rows}
    (base/(args.output+'.json')).write_text(json.dumps(payload, indent=2)+'\n', encoding='utf-8')
    figure_directory = base.parent if base.name == 'numerics' else base.parent.parent/'figures'
    with (figure_directory/(args.output+'.csv')).open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['lambda', f'slope_{args.depth-12}', f'slope_{args.depth}',
                         f'dimension_{args.depth-12}', f'dimension_{args.depth}', 'all_extinct', 'capped'])
        for r in rows:
            writer.writerow([r['lambda'], *r['estimates'].values(), *r['dimension_proxies'].values(), int(r['all_extinct']), int(r['capped'])])
    print('Saved', len(rows), 'samples in', round(time.time()-start, 1), 'seconds', flush=True)


if __name__ == '__main__':
    main()
