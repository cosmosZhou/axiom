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
    from Axiom import Sets, Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])), y)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.expr.simplify()

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Sets.All_Ne.to.Any.And.Cup.FiniteSet)

    a = Eq[-1].lhs.variable
    Eq << Algebra.Cond.to.Cond.subs.apply(Eq[2], x[:n], a[:n])

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(Algebra.Cond.Any.to.Any.And)

    Eq << Eq[-1].this.find(And).args[1:].apply(Algebra.Cond.Imply.to.Cond.trans)

    Eq << Any[y[n]](Equal(y[n], a[n]), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(Algebra.Cond.Any.to.Any.And)

    Eq << Eq[-1].this.find(And).args[:2].apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.find(Equal & Greater).apply(Algebra.Eq.Gt.to.Gt.trans, ret=0)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Any.Any.to.Any.And, simplify=0)

    Eq << Eq[-1].this.find(Equal[Cup]).apply(Sets.Eq_Cup.to.Eq.ReducedMax, ret=0, simplify=None)

    Eq << Eq[-1].this.find(And).args[1::2].apply(Algebra.Eq.Gt.to.Gt.trans, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(Sets.Eq.to.Eq.set, simplify=None)

    Eq << Eq[-1].this.find(And).args[:2].apply(Sets.Eq.Eq.to.Eq.Cup.push, simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, -1)

    Eq << Eq[-1].this.find(And).args[:2].apply(Algebra.Eq.Eq.to.Eq.trans, -1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash)

    Eq << Eq[-1].this.find(ReducedMax).apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(Less).apply(Algebra.LtMaxima.to.All.Lt)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.to.Cond.subs, i, n - 1)

    Eq << Eq[-1].this.find(And).args[1:].apply(Algebra.Cond.All.to.All.push)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any_And.to.Any.limits_absorb, 1)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], start=1, n=n)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-11-12
