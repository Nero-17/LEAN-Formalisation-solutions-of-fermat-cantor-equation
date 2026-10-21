from functools import lru_cache
S=1<<192
M=64

def ceildiv(a,b):return -((-a)//b)
@lru_cache(None)
def unitlog(x,y):
 # ln((1+x/y)/(1-x/y)), with0<=x/y<=1/3.
 assert 0<=3*x<=y
 lo=S*x//y;hi=ceildiv(S*x,y)
 lo2=lo*lo//S;hi2=ceildiv(hi*hi,S)
 pl,ph=lo,hi;sl,sh=0,0
 for j in range(M):
  sl+=pl//(2*j+1);sh+=ceildiv(ph,2*j+1)
  pl=pl*lo2//S;ph=ceildiv(ph*hi2,S)
 # Strict tail upper 3*(1/3)^(2M+1)/(2M+1)
 tail=ceildiv(3*S,(3**(2*M+1))*(2*M+1))
 return 2*sl,2*sh+tail
LOG2=unitlog(1,3)
@lru_cache(None)
def logint(k):
 assert k>=1
 e=k.bit_length()-1;p=1<<e
 a,b=unitlog(k-p,k+p)
 return e*LOG2[0]+a,e*LOG2[1]+b

def linearlog(terms):
 lo=hi=0
 for c,k in terms:
  a,b=logint(k)
  if c>=0:lo+=c*a;hi+=c*b
  else:lo+=c*b;hi+=c*a
 return lo,hi

def exact_fast(a,b,P,Q,J,bi):
 from thirdreal20261021_rational_scan import bands,F
 lo,hi=bands[bi]
 if not lo<F(a*Q,b*(P+1)) or not F(a*(Q+1),b*P)<hi:return False
 low=linearlog([(J,3),(b,b),(a,P),(-b,a),(-b,Q+1)])
 high=linearlog([(J,3),(b,b),(a,P+1),(-b,a),(-b,Q)])
 return low[1]<0 and high[0]>0

if __name__=='__main__':
 import json,time
 from pathlib import Path
 from thirdreal20261021_rational_scan import exact
 raw=json.loads(Path('work/thirdreal20261021_rational_scan_100.json').read_text());start=time.time()
 for row in raw['individual_sources']:
  assert exact_fast(*row)
 print('Fast rigorous log bounds PASS',len(raw['individual_sources']),time.time()-start,logint.cache_info())
