from util import *


@apply
def apply(imply):
    eqs, *limits = imply.of(Any[And])
    ps, qs = zip(*(eq.of(Imply) for eq in eqs))

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
        infers.append(Imply(p, Any(q, *limits)))

    return tuple(infers)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    p, q = Function(bool=True)
    Eq << apply(Any[x](Imply(j < i, p(x[i, j])) & Imply(j >= i, q(x[i, j]))))

    Eq <<= Algebra.Imply.to.Imply.And.apply(Eq[-2]), Algebra.Imply.to.Imply.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None), Eq[-1].this.rhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Algebra.Imply.Imply.to.Imply.Or.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].this.find(Imply).apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.find(Imply).apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.equ.Or)

    Eq << Algebra.Any_Or.of.OrAnyS.apply(Eq[-1])

    Eq << Eq[-1].this.find(And[Or]).apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.find(Any[Or]).apply(Algebra.Any_Or.of.OrAnyS)

    Eq << Eq[-1].this.args[:2].apply(Algebra.Or_Any.of.Any.Or)

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()
# created on 2023-07-01
