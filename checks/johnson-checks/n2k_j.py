exec(open('n2k.py').read().split("random.seed(5)")[0])
random.seed(7)
for k in [4,5]:
    n,V,nb=setup(k); N=len(V)
    for j in [2,4]:
        for _ in range(3):
            roots=random.sample(V,j); orb,sym=orbits(n,k,V,roots)
            psi=[[len(v&S) for v in V] for S in roots]; res=[]
            for d in [2,3,4]:
                mons=[]
                for e in itertools.product(range(d+1),repeat=j):
                    if 0<sum(e)<=d:
                        f=[1]*N
                        for r in range(j):
                            if e[r]: f=[f[i]*psi[r][i]**e[r] for i in range(N)]
                        mons.append(f)
                res.append(same(partition_of(mons+[Aop(f,nb) for f in mons],N),orb))
            print(f"J({n},{k}) {j} roots symmetric={sym}: orbits {len(set(orb))}; separated with degree<=2,3,4 (+A): {res}", flush=True)
