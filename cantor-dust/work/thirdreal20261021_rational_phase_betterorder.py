import thirdreal20261021_rational_phase_grouped as grouped
from alln20261020_verify_fixed_m import prefixes
import sys
original=prefixes
grouped.prefixes=lambda depth: sorted(original(depth),key=lambda p:(12*p<3**depth,p))
m=int(sys.argv[1]);grouped.grouped(m,m-1,1)
