from util import *


@apply
def apply(all_historic, y=None):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_historic.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    if y is None:
        y = all_historic.generate_var(**xi.dtype.dict, shape=(oo,))
    return Any[y[:n]:All[i:1:n](y[i - 1] < y[i])](Equal(Cup[i:n]({y[i]}), Cup[i:n]({xi})))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])), y)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.expr.simplify()

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.all_ne.imply.any.et.cup.finiteset)

    a = Eq[-1].lhs.variable
    Eq << algebra.cond.imply.cond.subs.apply(Eq[2], x[:n], a[:n])

    Eq << algebra.infer.given.et.infer.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(algebra.cond.any.imply.any.et)

    Eq << Eq[-1].this.find(And).args[1:].apply(algebra.cond.infer.imply.cond.transit)

    Eq << Any[y[n]](Equal(y[n], a[n]), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << algebra.infer.given.et.infer.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(algebra.cond.any.imply.any.et)

    Eq << Eq[-1].this.find(And).args[:2].apply(algebra.cond.any.imply.any.et, simplify=None)

    Eq << Eq[-1].this.find(Equal & Greater).apply(algebra.eq.gt.imply.gt.transit, ret=0)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.any.any.imply.any.et, simplify=0)

    Eq << Eq[-1].this.find(Equal[Cup]).apply(sets.eq_cup.imply.eq.reducedMax, ret=0, simplify=None)

    Eq << Eq[-1].this.find(And).args[1::2].apply(algebra.eq.gt.imply.gt.transit, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(sets.eq.imply.eq.set, simplify=None)

    Eq << Eq[-1].this.find(And).args[:2].apply(sets.eq.eq.imply.eq.cup.push, simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.any.imply.any.et.limits.unleash, -1)

    Eq << Eq[-1].this.find(And).args[:2].apply(algebra.eq.eq.imply.eq.transit, -1)

    Eq << Eq[-1].this.lhs.apply(algebra.any.imply.any.et.limits.unleash)

    Eq << Eq[-1].this.find(ReducedMax).apply(algebra.reducedMax.to.maxima)

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(Less).apply(algebra.maxima_lt.imply.all.lt)

    Eq << Eq[-1].this.find(All).apply(algebra.all.imply.cond.subs, i, n - 1)

    Eq << Eq[-1].this.find(And).args[1:].apply(algebra.cond.all.imply.all.push)

    Eq << Eq[-1].this.lhs.apply(algebra.any_et.imply.any.limits_absorb, 1)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], start=1, n=n)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-11-12