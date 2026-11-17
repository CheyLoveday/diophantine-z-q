import cmath
pi=cmath.pi
def th(tau,N=60):
    q=cmath.exp(pi*1j*tau)
    t3=sum(q**(n*n) for n in range(-N,N+1))
    t4=sum((-1)**n*q**(n*n) for n in range(-N,N+1))
    t2=sum(cmath.exp(pi*1j*tau*(n+0.5)**2) for n in range(-N,N))
    return t2,t3,t4
def E(k,tau,N=400):
    q=cmath.exp(2*pi*1j*tau); c={4:240,6:-504}[k]
    return 1+c*sum(n**(k-1)*q**n/(1-q**n) for n in range(1,N))
def eta(tau,N=400):
    q=cmath.exp(2*pi*1j*tau); p=1
    for n in range(1,N): p*=(1-q**n)
    return cmath.exp(pi*1j*tau/12)*p
def j(tau): return E(4,tau)**3/eta(tau)**24
for tau in [complex(0.1,0.06), complex(-0.3,0.045), complex(0.37,0.08)]:
    t2,t3,t4=th(tau); A,B,C=t2**4,t3**4,t4**4
    print("E4,E6", abs(E(4,tau)-(A**2+B**2+C**2)/2), abs(E(6,tau)-(B+C)*(A+B)*(C-A)/2))
    e=lambda d: eta(d*tau)
    x=e(2)**2*e(16)/(e(4)*e(32)**2)+2
    y=-(e(8)**4*e(16)**2/(e(4)**2*e(32)**4))
    T2,T3,T4=th(16*tau); a2,a3,a4=th(4*tau)
    print("curve",abs(y**2-x**3-4*x),"xth",abs(x-2*T3/T2),"yth",abs(y+a2**2/T2**2))
    a=-y; b=(x+2)**2/4
    A2=4*a*b; B2=(a+b)**2
    E4=A2**2+14*A2*B2+B2**2; E6=(A2+B2)*((A2+B2)**2-36*A2*B2)
    jj=j(tau); print("j rel err", abs(jj-1728*E4**3/(E4**3-E6**2))/abs(jj))
    s=x**2/4; u=s**2-1   # t^2
    # E4p, E6p polynomials in s and t^2 : compute with t=sqrt
    t=cmath.sqrt(u)
    Ap=((s-t)/2)**2; Bp=((s+t)/2)**2; Cp=s*t
    E4p=(Ap**2+Bp**2+Cp**2)/2; E6p=(Bp+Cp)*(Ap+Bp)*(Cp-Ap)/2
    j32=j(32*tau); print("j32 rel err", abs(j32-1728*E4p**3/(E4p**3-E6p**2))/abs(j32))
