# Produced for the AxiomProver formalization using AxiomCode.
import sys, math
def series(m, num, den, ell, N):
    # prod over j>=0 of prod_{a in num}(1-q^{mj+a})^ell / prod_{b in den}(1-q^{mj+b})^ell, coefficients up to N
    c=[0]*(N+1); c[0]=1
    exps_num=[]; exps_den=[]
    j=0
    while True:
        added=False
        for a in num:
            e=m*j+a
            if e<=N: exps_num.append(e); added=True
        for b in den:
            e=m*j+b
            if e<=N: exps_den.append(e); added=True
        if not added: break
        j+=1
    for _ in range(ell):
        for e in exps_num:
            for n in range(N,e-1,-1): c[n]-=c[n-e]
        for e in exps_den:
            for n in range(e,N+1): c[n]+=c[n-e]
    return c
def sgn(x): return (x>0)-(x<0)
if __name__=="__main__":
  pass
N=int(sys.argv[1]) if len(sys.argv)>1 else 1500
bad=0
# Cor 1.2
for m in [5,7,9,11,13,15,19,21,25]:
  for ell in range(1,8):
    if not m>6*ell: continue
    c=series(m,[1,m-1],[2,m-2],ell,N)
    if ell%2==0: S=(m+1)//2-5*ell//2, (3*m-1)//2-5*ell//2
    else: S=m-(5*ell-1)//2, 2*m-(5*ell+1)//2
    errs=[n for n in range(N-4*m,N+1) if sgn(c[n])!=(-1)**((n%(2*m))+ell//2+(1 if S[0]<=n%(2*m)<=S[1] else 0))]
    # also check thm1.1 sign formula
    phi=0.5*(1-2/m)*(1-3/m)
    errs2=[n for n in range(N-4*m,N+1) if sgn(c[n])!=(-1)**n*sgn(math.cos(math.pi*(phi*ell-n/m)))]
    if errs or errs2: bad+=1; print("Cor1.2/Thm1.1 FAIL",m,ell,errs[:5],errs2[:5])
# Cor1.4
for m in [4,6,8,10,12]:
  for ell in range(1,5):
    c=series(m,[1,m-1],[2,m-2],ell,400)
    errs=[n for n in range(401) if sgn(c[n])!=(-1)**n]
    if errs: bad+=1; print("Cor1.4 FAIL",m,ell,errs[:5])
# Cor1.6
def jac3(m): return 1 if m%3==1 else -1
for m in [5,7,11,13,17,19,23,25,29,31,35]:
  pm = 1 if m%6==1 else -1   # m ≡ ±1 mod 6 ; upper sign <-> m≡1
  for lam in range(1,40):
    if not lam < m/2: continue
    g=series(m,[2,m-2],[1,m-1],lam,N)
    a=lam%6
    def S(a):
        p=pm
        if a==0: return ((m+1)/2+lam/6,(3*m-1)/2+lam/6)
        if a==1: return (((3-p)*m+4)/6+(lam-1)/6, ((9-p)*m-2)/6+(lam-1)/6)
        if a==2: return (((3-2*p)*m+5)/6+(lam-2)/6, ((9-2*p)*m-1)/6+(lam-2)/6)
        if a==3: return ((lam+3)/6, m+(lam-3)/6)
        if a==4: return (((3+2*p)*m+7)/6+(lam-4)/6, ((9+2*p)*m+1)/6+(lam-4)/6)
        if a==5: return (((3+p)*m+8)/6+(lam-5)/6, ((9+p)*m+2)/6+(lam-5)/6)
    lo,hi=S(a)
    eps = 1 if a in (0,1,2) else (-1 if a in (4,5) else jac3(m))
    errs=[]; errs2=[]
    for n in range(N-12*m,N+1):
        # n ≡ 3r+2mj mod 6m
        found=None
        for r in range(2*m):
            for j in range(3):
                if (3*r+2*m*j-n)%(6*m)==0: found=r
        r=found
        pred=(-1)**(r+lam//6+(1 if lo<=r<=hi else 0))*eps
        if sgn(g[n])!=pred: errs.append(n)
        T=math.cos(math.pi*(lam/6-n/3+pm*((2*n-lam)/(6*m)+lam/m**2)))
        if sgn(g[n])!=sgn(T): errs2.append(n)
    if errs or errs2: bad+=1; print("Cor1.6/Thm1.5 FAIL m",m,"lam",lam,"cor",errs[:4],"thm",errs2[:4])
print("bad",bad)
