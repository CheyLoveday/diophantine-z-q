from fractions import Fraction as Q
from math import factorial
import json
from pathlib import Path
# e^5 > sum through degree 6 > 100, used with pi>3, sqrt(3)>5/3.
e5_lower=sum(Q(5**n,factorial(n)) for n in range(7))
assert e5_lower>100
assert Q(200,9801)+Q(1,10)<1
assert 64*2**2==256 and 1024*2**3==8192 and 8192//2==4096
assert 256*4+2*2==1028 and 1+2*2==5 and 2*42000==84000
assert Q(208**3,2304)==Q(35152,9) and 35152%9!=0
# log16<4, so 1000*16*log(16)^5 < 1000*2^14 < 1000*2^24.
assert 16*4**5 < 2**24
# X_D <= 3X; (1/2+2C2)*3 <= 10000*2^24.
assert (Q(1,2)+2*1000*2**24)*3 < 10000*2**24
v=40*10000*2**24+96
assert v<10**13
out={'e5_rational_lower':str(e5_lower),'theta_final_constant':v,'j_invariant':str(Q(208**3,2304)),'all_assertions_passed':True}
Path(__file__).with_name('acceptance-exact-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
