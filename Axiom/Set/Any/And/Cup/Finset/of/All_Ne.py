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
    from Axiom import Algebra, Set, Logic

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n + 1](Unequal(x[i], x[j])), y)

    Eq << Eq[1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(ReducedMax).apply(Algebra.ReducedMax.eq.Maxima, i)

    Eq << Eq[-1].this.find(Less).apply(Algebra.LtMaxima.given.All.Lt)

    Eq << Eq[-1].this.find(Less).reversed

    k = Symbol(ReducedArgMax(x[:n + 1]))
    Eq.k_def = k.this.definition

    Eq << Algebra.Any.given.Cond.subs.apply(Eq[-1], y[:n + 1], Lamda[i:n + 1](Piecewise((x[i], i < k), (x[i + 1], i < n), (x[k], True))))

    Eq.eq, Eq.all_gt, Eq.all_ne = Algebra.And.given.And.apply(Eq[-1], None)

    Eq << Eq.eq.this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.lhs.apply(Set.Cup.eq.Union.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Cup)().find(GreaterEqual).simplify()

    Eq << Eq[-1].this.lhs.find(Cup).expr.apply(Set.Finset.eq.Ite)

    Eq << Eq[-1].this.lhs.args[1].apply(Set.Cup.limits.subs.offset, -1)

    Eq << Eq.all_gt.this.expr.apply(Algebra.Gt.given.And)

    Eq.all_ne_piece, Eq.all_ge = Algebra.All_And.given.And.All.apply(Eq[-1])

    Eq << Logic.All.given.Imp.apply(Eq.all_ne_piece)

    Eq << Eq[-1].this.rhs.apply(Logic.Cond_Ite.given.And.Imp)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq <<= Eq[-2].this.lhs.apply(Set.Mem.Range.Inter.of.Lt.Mem_Range), Eq[-1].this.lhs.apply(Set.Mem.Range.Inter.of.Ge.Mem_Range)

    Eq <<= Logic.Imp.given.All.apply(Eq[-2]), Logic.Imp.given.All.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << Algebra.Cond.of.All.subs.apply(Eq[0], i, k)

    Eq << Eq[0].this.apply(Algebra.All.limits.swap.intlimit)

    Eq << Algebra.Cond.of.All.subs.apply(Eq[-1], j, k)

    Eq << Eq[-1].this.expr.reversed

    Eq << Logic.All.given.Imp.apply(Eq.all_ge)

    Eq << Eq[-1].this.rhs.apply(Logic.Cond_Ite.given.And.Imp)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq <<= Eq[-2].this.lhs.apply(Set.Mem.Range.Inter.of.Lt.Mem_Range), Eq[-1].this.lhs.apply(Set.Mem.Range.Inter.of.Ge.Mem_Range)

    Eq <<= Logic.Imp.given.All.apply(Eq[-2]), Logic.Imp.given.All.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(i, i - 1)

    Eq << Algebra.All.Ge.of.Eq_ReducedArgMax.apply(Eq.k_def)

    Eq << Algebra.And.All.of.All.split.apply(Eq[-1], cond=i < k)

    Eq << Algebra.All.of.All.limits.restrict.apply(Eq[-1], Range(k + 1, n + 1))

    Eq << Logic.All.given.Imp.apply(Eq.all_ne)

    Eq << Eq[-1].this.rhs.apply(Logic.Cond_Ite.given.And.Imp)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq <<= Eq[-2].this.lhs.args[::2].apply(Set.Mem.Range.Inter.of.Lt.Mem_Range), Eq[-1].this.lhs.args[::2].apply(Set.Mem.Range.Inter.of.Ge.Mem_Range)

    Eq <<= Eq[-2].this.rhs.apply(Logic.Cond_Ite.given.And.Imp), Eq[-1].this.rhs.apply(Logic.Cond_Ite.given.And.Imp)

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-2]), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-4].this.apply(Logic.Imp.flatten), Eq[-3].this.apply(Logic.Imp.flatten), Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Eq[-2].this.find(Element[2]).apply(Set.Gt.of.Mem_Range.domain)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(Set.Mem.Range.Inter.of.Lt.Mem_Range), \
        Eq[-3].this.lhs.args[:2].apply(Set.Mem.Range.Inter.of.Ge.Mem_Range),\
        Eq[-1].this.lhs.args[:2].apply(Set.Mem.Range.Inter.of.Ge.Mem_Range)

    Eq <<= Eq[-3].this.apply(Logic.Imp.fold, 0),\
        Eq[-2].this.apply(Logic.Imp.fold, 0),\
        Eq[-1].this.apply(Logic.Imp.fold, 0)

    Eq <<= Logic.Imp.given.All.apply(Eq[-3]), \
        Logic.Imp.given.All.apply(Eq[-2]), \
        Logic.Imp.given.All.apply(Eq[-1])

    Eq <<= Eq[-3].this.expr.apply(Logic.Imp.given.All), \
        Eq[-2].this.expr.apply(Logic.Imp.given.All), \
        Eq[-1].this.expr.apply(Logic.Imp.given.All)

    Eq <<= Algebra.All.given.All.limits.relax.apply(Eq[-3], (j, 0, i)),\
        Eq[-2].limits_subs(i, i - 1),\
        Eq[-1].limits_subs(i, i - 1).limits_subs(j, j - 1)

    Eq << Algebra.All.given.All.limits.relax.apply(Eq[-3], (i, 0, n + 1))

    Eq <<= Algebra.All.given.All.limits.relax.apply(Eq[-2], (j, 0, i)), Algebra.All.given.All.limits.relax.apply(Eq[-1], (j, 0, i))

    Eq <<= Algebra.All.given.All.limits.relax.apply(Eq[-1], (i, 0, n + 1))




if __name__ == '__main__':
    run()
# created on 2023-11-12
