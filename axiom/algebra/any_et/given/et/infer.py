from util import *


@apply
def apply(imply):
    eqs, *limits = imply.of(Any[And])
    ps, qs = zip(*(eq.of(Infer) for eq in eqs))
    
    cond = S.false
    for i in range(len(ps)):
        cond |= ps[i] 
        for j in range(i):
            if ps[i] & ps[j] == False:
                continue
            return

    assert cond
    
    variables = [v for v, *_ in limits]
    infers = []
    for p, q  in zip(ps, qs):
        assert not p.has(*variables)
        infers.append(Infer(p, Any(q, *limits)))
        
    return tuple(infers)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    p, q = Function(bool=True)
    Eq << apply(Any[x](Infer(j < i, p(x[i, j])) & Infer(j >= i, q(x[i, j]))))

    Eq <<= algebra.infer.imply.infer.et.apply(Eq[-2]), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.cond.any.imply.any.et, simplify=None), Eq[-1].this.rhs.apply(algebra.cond.any.imply.any.et, simplify=None)

    Eq << algebra.infer.infer.imply.infer.ou.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].this.find(Infer).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.find(Infer).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.find(And).apply(algebra.et.to.ou)

    Eq << algebra.any_ou.given.ou.any.apply(Eq[-1])

    Eq << Eq[-1].this.find(And[Or]).apply(algebra.et.to.ou)

    Eq << Eq[-1].this.find(Any[Or]).apply(algebra.any_ou.given.ou.any)

    Eq << Eq[-1].this.args[:2].apply(algebra.ou_any.given.any.ou)

    Eq << algebra.ou.given.cond.apply(Eq[-1], 1)

    


if __name__ == '__main__':
    run()
# created on 2023-07-01
