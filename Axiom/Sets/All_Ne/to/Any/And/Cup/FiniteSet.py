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
    from Axiom import Algebra, Sets

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n + 1](Unequal(x[i], x[j])), y)

    Eq << Eq[1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(ReducedMax).apply(Algebra.ReducedMax.eq.Maxima, i)

    Eq << Eq[-1].this.find(Less).apply(Algebra.LtMaxima.of.All.Lt)

    Eq << Eq[-1].this.find(Less).reversed

    k = Symbol(ReducedArgMax(x[:n + 1]))
    Eq.k_def = k.this.definition

    Eq << Algebra.Any.of.Cond.subs.apply(Eq[-1], y[:n + 1], Lamda[i:n + 1](Piecewise((x[i], i < k), (x[i + 1], i < n), (x[k], True))))

    Eq.eq, Eq.all_gt, Eq.all_ne = Algebra.And.of.And.apply(Eq[-1], None)

    Eq << Eq.eq.this.find(Piecewise).apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.lhs.apply(Sets.Cup.eq.Union.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Cup)().find(GreaterEqual).simplify()

    Eq << Eq[-1].this.lhs.find(Cup).expr.apply(Sets.FiniteSet.eq.Piece)

    Eq << Eq[-1].this.lhs.args[1].apply(Sets.Cup.limits.subs.offset, -1)

    Eq << Eq.all_gt.this.expr.apply(Algebra.Gt.of.And)

    Eq.all_ne_piece, Eq.all_ge = Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Algebra.All.of.Imply.apply(Eq.all_ne_piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.And.Imply)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Eq[-2].this.lhs.apply(Sets.Lt.In_Range.to.In.Range.Intersect), Eq[-1].this.lhs.apply(Sets.Ge.In_Range.to.In.Range.Intersect)

    Eq <<= Algebra.Imply.of.All.apply(Eq[-2]), Algebra.Imply.of.All.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << Algebra.All.to.Cond.subs.apply(Eq[0], i, k)

    Eq << Eq[0].this.apply(Algebra.All.limits.swap.intlimit)

    Eq << Algebra.All.to.Cond.subs.apply(Eq[-1], j, k)

    Eq << Eq[-1].this.expr.reversed

    Eq << Algebra.All.of.Imply.apply(Eq.all_ge)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.And.Imply)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Eq[-2].this.lhs.apply(Sets.Lt.In_Range.to.In.Range.Intersect), Eq[-1].this.lhs.apply(Sets.Ge.In_Range.to.In.Range.Intersect)

    Eq <<= Algebra.Imply.of.All.apply(Eq[-2]), Algebra.Imply.of.All.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << Algebra.Eq_ReducedArgMax.to.All.Ge.apply(Eq.k_def)

    Eq << Algebra.All.to.And.All.split.apply(Eq[-1], cond=i < k)

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], Range(k + 1, n + 1))

    Eq << Algebra.All.of.Imply.apply(Eq.all_ne)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.And.Imply)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq <<= Eq[-2].this.lhs.args[::2].apply(Sets.Lt.In_Range.to.In.Range.Intersect), Eq[-1].this.lhs.args[::2].apply(Sets.Ge.In_Range.to.In.Range.Intersect)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Cond_Piece.of.And.Imply), Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.And.Imply)

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-2]), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-4].this.apply(Algebra.Imply.flatten), Eq[-3].this.apply(Algebra.Imply.flatten), Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-2].this.find(Element[2]).apply(Sets.In_Range.to.Gt.domain)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(Sets.Lt.In_Range.to.In.Range.Intersect), \
        Eq[-3].this.lhs.args[:2].apply(Sets.Ge.In_Range.to.In.Range.Intersect),\
        Eq[-1].this.lhs.args[:2].apply(Sets.Ge.In_Range.to.In.Range.Intersect)

    Eq <<= Eq[-3].this.apply(Algebra.Imply.fold, 0),\
        Eq[-2].this.apply(Algebra.Imply.fold, 0),\
        Eq[-1].this.apply(Algebra.Imply.fold, 0)

    Eq <<= Algebra.Imply.of.All.apply(Eq[-3]), \
        Algebra.Imply.of.All.apply(Eq[-2]), \
        Algebra.Imply.of.All.apply(Eq[-1])

    Eq <<= Eq[-3].this.expr.apply(Algebra.Imply.of.All), \
        Eq[-2].this.expr.apply(Algebra.Imply.of.All), \
        Eq[-1].this.expr.apply(Algebra.Imply.of.All)

    Eq <<= Algebra.All.of.All.limits.relax.apply(Eq[-3], (j, 0, i)),\
        Eq[-2].limits_subs(i, i - 1),\
        Eq[-1].limits_subs(i, i - 1).limits_subs(j, j - 1)

    Eq << Algebra.All.of.All.limits.relax.apply(Eq[-3], (i, 0, n + 1))

    Eq <<= Algebra.All.of.All.limits.relax.apply(Eq[-2], (j, 0, i)), Algebra.All.of.All.limits.relax.apply(Eq[-1], (j, 0, i))

    Eq <<= Algebra.All.of.All.limits.relax.apply(Eq[-1], (i, 0, n + 1))




if __name__ == '__main__':
    run()
# created on 2023-11-12
