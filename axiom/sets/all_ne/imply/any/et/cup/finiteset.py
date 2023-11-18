from util import *


@apply
def apply(all_historic, y=None):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_historic.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    if y is None:
        y = all_historic.generate_var(**xi.dtype.dict, shape=(oo,))
    return Any[y[:n]:Equal(Cup[i:n]({y[i]}), Cup[i:n]({xi}))](All[j:i, i:n - 1](Unequal(y[i], y[j])) & (y[n - 1] > ReducedMax(y[:n - 1])))


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n + 1](Unequal(x[i], x[j])), y)

    Eq << Eq[1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(ReducedMax).apply(algebra.reducedMax.to.maxima, i)

    Eq << Eq[-1].this.find(Less).apply(algebra.maxima_lt.given.all.lt)

    Eq << Eq[-1].this.find(Less).reversed

    k = Symbol(ReducedArgMax(x[:n + 1]))
    Eq.k_def = k.this.definition

    Eq << algebra.any.given.cond.subs.apply(Eq[-1], y[:n + 1], Lamda[i:n + 1](Piecewise((x[i], i < k), (x[i + 1], i < n), (x[k], True))))

    Eq.eq, Eq.all_gt, Eq.all_ne = algebra.et.given.et.apply(Eq[-1], None)

    Eq << Eq.eq.this.find(Piecewise).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Cup)().find(GreaterEqual).simplify()

    Eq << Eq[-1].this.lhs.find(Cup).expr.apply(sets.finiteset.to.piece)

    Eq << Eq[-1].this.lhs.args[1].apply(sets.cup.limits.subs.offset, -1)

    Eq << Eq.all_gt.this.expr.apply(algebra.gt.given.et)

    Eq.all_ne_piece, Eq.all_ge = algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << algebra.all.given.infer.apply(Eq.all_ne_piece)

    Eq << Eq[-1].this.rhs.apply(algebra.cond_piece.given.et.infer)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= Eq[-2].this.lhs.apply(sets.lt.el_range.imply.el.range.intersect), Eq[-1].this.lhs.apply(sets.ge.el_range.imply.el.range.intersect)

    Eq <<= algebra.infer.given.all.apply(Eq[-2]), algebra.infer.given.all.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], i, k)

    Eq << Eq[0].this.apply(algebra.all.limits.swap.intlimit)

    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], j, k)

    Eq << Eq[-1].this.expr.reversed

    Eq << algebra.all.given.infer.apply(Eq.all_ge)

    Eq << Eq[-1].this.rhs.apply(algebra.cond_piece.given.et.infer)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= Eq[-2].this.lhs.apply(sets.lt.el_range.imply.el.range.intersect), Eq[-1].this.lhs.apply(sets.ge.el_range.imply.el.range.intersect)

    Eq <<= algebra.infer.given.all.apply(Eq[-2]), algebra.infer.given.all.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << algebra.eq_reducedArgMax.imply.all.ge.apply(Eq.k_def)

    Eq << algebra.all.imply.et.all.split.apply(Eq[-1], cond=i < k)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], Range(k + 1, n + 1))

    Eq << algebra.all.given.infer.apply(Eq.all_ne)

    Eq << Eq[-1].this.rhs.apply(algebra.cond_piece.given.et.infer)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= Eq[-2].this.lhs.args[::2].apply(sets.lt.el_range.imply.el.range.intersect), Eq[-1].this.lhs.args[::2].apply(sets.ge.el_range.imply.el.range.intersect)

    Eq <<= Eq[-2].this.rhs.apply(algebra.cond_piece.given.et.infer), Eq[-1].this.rhs.apply(algebra.cond_piece.given.et.infer)

    Eq <<= algebra.infer.given.et.infer.apply(Eq[-2]), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-4].this.apply(algebra.infer.flatten), Eq[-3].this.apply(algebra.infer.flatten), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-2].this.find(Element[2]).apply(sets.el_range.imply.gt.domain)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(sets.lt.el_range.imply.el.range.intersect), \
        Eq[-3].this.lhs.args[:2].apply(sets.ge.el_range.imply.el.range.intersect),\
        Eq[-1].this.lhs.args[:2].apply(sets.ge.el_range.imply.el.range.intersect)

    Eq <<= Eq[-3].this.apply(algebra.infer.fold, 0),\
        Eq[-2].this.apply(algebra.infer.fold, 0),\
        Eq[-1].this.apply(algebra.infer.fold, 0)

    Eq <<= algebra.infer.given.all.apply(Eq[-3]), \
        algebra.infer.given.all.apply(Eq[-2]), \
        algebra.infer.given.all.apply(Eq[-1])

    Eq <<= Eq[-3].this.expr.apply(algebra.infer.given.all), \
        Eq[-2].this.expr.apply(algebra.infer.given.all), \
        Eq[-1].this.expr.apply(algebra.infer.given.all)

    Eq <<= algebra.all.given.all.limits.relax.apply(Eq[-3], (j, 0, i)),\
        Eq[-2].limits_subs(i, i - 1),\
        Eq[-1].limits_subs(i, i - 1).limits_subs(j, j - 1)

    Eq << algebra.all.given.all.limits.relax.apply(Eq[-3], (i, 0, n + 1))

    Eq <<= algebra.all.given.all.limits.relax.apply(Eq[-2], (j, 0, i)), algebra.all.given.all.limits.relax.apply(Eq[-1], (j, 0, i))

    Eq <<= algebra.all.given.all.limits.relax.apply(Eq[-1], (i, 0, n + 1))

    


if __name__ == '__main__':
    run()
# created on 2023-11-12
