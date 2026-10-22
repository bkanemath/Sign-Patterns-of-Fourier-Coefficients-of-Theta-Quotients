# Produced for the AxiomProver formalization using AxiomCode.
import cmath, math
pi=math.pi; I=1j
def theta(w,tau,K=60):
    s=0
    for k in range(-K,K):
        e=pi*I*(k+0.5)**2*tau+2*pi*I*(k+0.5)*(w+0.5)
        if e.real>-745: s+=cmath.exp(e)
    return s
def poch(a,q,N=400):
    p=1
    for n in range(N): p*=1-a*q**n
    return p
# E2(3) triple product
for (w,tau) in [(0.3+0.1j,0.2+0.9j),(1.7-0.4j,-0.3+0.5j)]:
    q=cmath.exp(2*pi*I*tau); z=cmath.exp(2*pi*I*w)
    rhs=-I*cmath.exp(pi*I*tau/4)*cmath.exp(-pi*I*w)*poch(q,q)*poch(z,q)*poch(q/z,q)
    print("E2(3)",abs(theta(w,tau)-rhs))
# E2(1)
for (h,k,hp,z) in [(1,3,2,0.37),(2,5,2,0.21),(0,1,0,0.5),(3,7,2,0.3),(-4,7,2,0.3)]:
    assert (h*hp+1)%k==0
    tau=(h+I*z)/k; tau1=(hp+I/z)/k
    vals=[theta(w,tau)/(cmath.exp(-pi*k*w**2/z)*theta(I*w/z,tau1)) for w in (0.1,0.3+0.2j,-0.7+0.05j)]
    print("E2(1)",h,k,[f"{v:.6f}" for v in vals])
# E3(3)
for (a,b) in [(0.2,0.4),(2/5,0.8),(-0.3,0.55)]:
    z=0.02
    lhs=theta(a*I*z+b,I*z,K=200)
    rhs=-cmath.exp(-2*pi*I*a*b+pi*I*a)*cmath.exp((-b*b-0.25+b)*pi/z)/math.sqrt(z)
    print("E3(3)",lhs/rhs)
# E3(4) complex z in cone
for a in (0.2,0.5,1.3):
    z=0.02*(1+0.5j)
    lhs=theta(a*I*z,I*z,K=200); rhs=-2*I*math.sin(pi*a)*cmath.exp(-pi/(4*z))/cmath.sqrt(z)
    print("E3(4)",lhs/rhs)
# E3(1),(2)
x0=0.3
for (a,b) in [(0.3,0.2),(0.7,-1.1)]:
    y=6; tau=x0+I*y
    print("E3(1)",theta(a*tau+b,tau)/(-I*cmath.exp(-pi*I*b)*cmath.exp(2*pi*I*tau*(1/8-a/2))))
for b in (0.3,2.6):
    y=6; tau=x0+I*y
    print("E3(2)",theta(b,tau)/(-2*math.sin(pi*b)*cmath.exp(pi*I*tau/4)))
# E6
z=0.03*(1-0.4j); q=cmath.exp(-z)
print("E6",poch(q,q,N=4000)/(cmath.sqrt(2*pi/z)*cmath.exp(-pi**2/(6*z))))
