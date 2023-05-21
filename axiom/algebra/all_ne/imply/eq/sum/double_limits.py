from util import *


@apply
def apply(all_ne, sgm):
    (ai, aj), (j, S[0], i), (S[i], S[0], n) = all_ne.of(All[Unequal])
    if ai._has(j):
        ai, xj = aj, ai

    assert ai._subs(i, j) == aj

    fx, (x, X) = sgm.of(Sum)

    _ai, (_i, S[0], n) = X.of(Cup[FiniteSet])
    assert _ai._subs(_i, i) == ai

    return Equal(sgm, Sum[i:n](fx._subs(x, ai)))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].cup_finiteset()
    Eq << apply(All[j:i, i:n](Unequal(a[i], a[j])), Sum[x:s](f(x)))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.find(All).apply(algebra.all_ne.imply.eq.sum, Eq.hypothesis.rhs.lhs)

    Eq << Eq[-1].this.lhs.find(Equal).apply(algebra.eq.transport, rhs=0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq.hypothesis, cond=Eq[-1].lhs.find(Equal))

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.add.to.sum.limits.push)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)

    
    


if __name__ == '__main__':
    run()
# created on 2019-02-05
# updated on 2023-05-21
