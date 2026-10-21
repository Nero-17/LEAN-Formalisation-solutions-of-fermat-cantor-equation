"""Finite-cylinder onset proxy; not a proof of Hausdorff positivity."""
from pathlib import Path
from fractions import Fraction
import json,time,csv,math
import check_transition_precision as precise
from scan_last_transition import candidate_m,local_counts
base=Path(__file__).parent

def survives(frac,lam,kmax=12):
    n=precise.mp.mpf(frac.numerator)/frac.denominator
    lm=precise.mp.mpf(str(lam))
    tried=[]
    for k in range(kmax+1):
        for m in candidate_m(float(frac),lam,k):
            cheap=local_counts(float(frac),lam,k,m,18,1000)
            if not cheap['counts'][-1]:continue
            r=precise.local(n,lm,k,m,depth=52,cap=512)
            tried.append(r)
            if r['counts'][-1]:return {'survives':True,'source':[k,m],'counts':r['counts'],'slope':r['slope'],'tried':tried}
    return {'survives':False,'tried':tried}

if __name__=='__main__':
    out=base/'first-transition-scan.jsonl'
    done={r['n'] for r in map(json.loads,out.read_text().splitlines())} if out.exists() else set()
    fractions=sorted({Fraction(a,b) for b in range(1,4) for a in range(2*b,8*b+1)})
    for frac in fractions:
        if str(frac) in done:continue
        if frac in [2,4]:
            row={'n':str(frac),'kind':'exact','estimate':2-math.sqrt(3) if frac==2 else .25}
        else:
            start=time.time(); checks=[]; hit=None
            # Offset grid avoids treating the known zero-dimensional critical
            # fibre at lambda=1/4 as an observed positive-dimensional fibre.
            for j in range(200):
                lam=round(.2501+.0005*j,7)
                r=survives(frac,lam)
                checks.append({'lambda':lam,'stage':'coarse',**r})
                if r['survives']:hit=lam;break
            if hit is None:raise RuntimeError(f'No numerical onset found for {frac}')
            lower=max(.25,round(hit-.0005,7))
            fine_hit=hit
            for j in range(1,6):
                lam=round(lower+.0001*j,7)
                if lam>hit+1e-9:break
                r=survives(frac,lam,kmax=24)
                checks.append({'lambda':lam,'stage':'fine',**r})
                if r['survives']:fine_hit=lam;break
            row={'n':str(frac),'kind':'numerical','estimate':max(.25,fine_hit-.00005),
                 'first_surviving_parameter':fine_hit,'grid_step':.0001,'depth':52,
                 'precision_digits':50,'kmax':24,'checks':checks,'seconds':time.time()-start}
        with out.open('a') as f:f.write(json.dumps(row)+'\n')
        print(row['n'],row['estimate'],row.get('seconds',0),flush=True)
    rows={r['n']:r for r in map(json.loads,out.read_text().splitlines())}
    dest=base.parent.parent/'figures'/'first-transition-estimates.csv'
    with dest.open('w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=['n','kind','estimate','first_surviving_parameter','grid_step','depth','precision_digits','kmax'])
        writer.writeheader()
        for frac in fractions:
            r=rows[str(frac)];writer.writerow({key:r.get(key,'') for key in writer.fieldnames})
    print(dest)
