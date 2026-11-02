"""Largest Lipschitz constant allowed by Theorem 5.11 of the paper (tex/) for the non-degenerate rational
tables with minimal n = 5..12 (r = 1), and for rational approximants of the trapezoid of Theorem 5.7
(Remark 5.13(c)). Usage: python3 orbit_slopes.py"""
import numpy as np, itertools, math
def table(n,idx):
    th=[2*math.pi*i/n for i in idx]; e=[complex(math.cos(t),math.sin(t)) for t in th]
    A,B,C,D=e
    M=np.array([[ (A-C).real, -(B-D).real],[(A-C).imag, -(B-D).imag]])
    tau,mu=np.linalg.solve(M,[(D-C).real,(D-C).imag])
    c=[tau,-mu,1-tau,-(1-mu)]
    m=lambda k: -sum(ci*ei**k for ci,ei in zip(c,e))
    res=[s for s in range(n) if s%n not in (0,1,n-1)]
    sig=min(abs(m(s)) for s in res)
    d1,d2=abs(A-C),abs(B-D); u=(A-C)/d1; v=(B-D)/d2
    g=abs((u.conjugate()*v).real); K=math.sqrt(2/(1-g))
    return sig,K,min(d1,d2),d1,d2
def maxL(n,sig,K,dm,r=1):
    def ok(L):
        t=math.sqrt(2)*K*L; lam=4/math.sqrt(3)*r/dm*K*L*t; eta=4/math.sqrt(3)*r*L*t
        if t>0.5 or lam>=1: return False
        A=2*K*math.sqrt(n)/(sig*dm*(1-lam)); return (n+1)*A*eta<1
    lo,hi=0,1
    for _ in range(60):
        mid=(lo+hi)/2
        if ok(mid): lo=mid
        else: hi=mid
    return lo
seen=set()
for n in range(5,13):
    best=None; worst=None; cnt=0; degen=[]
    for idx in itertools.combinations(range(n),4):
        if math.gcd(math.gcd(*idx[1:]),n)!=1 or idx[0]!=0: continue
        # canonical up to rotation/reflection
        key=(n,)+min(tuple(sorted(((s*i+a)%n) for i in idx)) for s in (1,-1) for a in range(n))
        if key in seen: continue
        seen.add(key)
        sig,K,dm,d1,d2=table(n,idx)
        if sig<1e-9: degen.append(idx); continue
        L=maxL(n,sig,K,dm); cnt+=1
        rec=(L,idx,sig,K,dm,abs(d1-d2)<1e-9); print("   ",n,idx,"L=%.4f"%L,"%.2f deg"%math.degrees(math.atan(L)),"sigma=%.3f K=%.3f dmin=%.3f"%(sig,K,dm),"eqdiag" if abs(d1-d2)<1e-9 else "")
        if best is None or L>best[0]: best=rec
        if worst is None or L<worst[0]: worst=rec
    f=lambda L: math.degrees(math.atan(L))
    print(n,'#nondeg',cnt,'best L %.4f (%.2f deg)'%(best[0],f(best[0])),best[1:],' worst L %.4f (%.2f deg)'%(worst[0],f(worst[0])),worst[1],'degen',degen)

print("approximants of the trapezoid of Thm 5.7")
al=math.acos(3/5); be=math.acos((math.sqrt(23)-3)/10)
angs=[al,2*math.pi-al,2*math.pi-be,be]  # A,B,C,D angles in [0,2pi); rotate so A=0
for n in [12,24,48,96,192,384,768]:
    idx=[round((a-al)%(2*math.pi)*n/(2*math.pi))%n for a in angs]
    if len(set(idx))<4: continue
    sig,K,dm,d1,d2=table(n,idx)
    L=maxL(n,sig,K,dm) if sig>1e-9 else 0
    print(n,idx,"sigma=%.4f L=%.5f (%.3f deg)"%(sig,L,math.degrees(math.atan(L))))
