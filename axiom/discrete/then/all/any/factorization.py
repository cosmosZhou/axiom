from util import *


@apply
def apply(n):
    i = Symbol(integer=True)

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    b = Symbol(integer=True, shape=(oo,), nonnegative=True)

    return All[p[:n]:P](Any[b[:n]](Equal(p[:n], Lamda[i:n](i) @ MatProduct[i:n](SwapMatrix(n, i, b[i])))))


@prove
def prove(Eq):
    from axiom import algebra, sets, discrete

    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(n)

    b = Eq[1].expr.variable.base
    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.doit(deep=True)

    Eq << Eq[-1].this.find(Sliced).apply(algebra.slice.to.matrix)

    Eq << Eq[-1].this.find(Sliced).apply(algebra.slice.to.matrix)

    Eq << Eq[-1].this.find(Sliced).apply(algebra.slice.to.matrix)

    p0 = Eq[-1].variable
    Eq << Eq[-1].this.expr.apply(algebra.any.of.cond.subs, b[:2], Matrix((0, KroneckerDelta(p0, 0))))

    Eq << Eq[-1].this.expr.rhs.expand()

    Eq << Eq[-1].this.expr.rhs[0].simplify()

    Eq.equation = Eq[-1].this.expr.rhs[1].simplify()

    Eq.limits_assertion = algebra.then.all.limits_assert.apply(Eq.equation.limits)

    Eq << Eq.limits_assertion.this.expr.apply(sets.eq.then.eq.split.finiteset.add)

    Eq.p1_equality = Eq[-1].this.expr - p0

    Eq <<= Eq.equation & Eq.p1_equality

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.all_et.of.et.all.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.of.et.split.matrix)

    Eq.premier, Eq.second = algebra.all_et.of.et.all.apply(Eq[-1])

    Eq << Eq.limits_assertion.this.expr.apply(sets.eq.then.et.split.finiteset)

    Eq << algebra.all_et.then.et.all.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(sets.el.then.eq.delta.zero).reversed

    Eq << -(Eq.premier - 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.expr.expr.rhs.args[1].this.apply(discrete.matProd.to.matmul.pop)

    Eq << discrete.block.to.matProd.apply(n, n, b)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(algebra.lamda.to.block.pop)

    Eq << MatMul(*Eq[-1].expr.expr.rhs.args[:2]).this.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.deduction = Eq[-1].this.expr.expr @ Eq[-1].expr.expr.rhs.args[1]

    Eq << discrete.then.all.any.permutation.any.basic.apply(n + 1)

    Eq << Eq[-1].this.expr.limits_subs(Eq[-1].expr.variable, b[n])

    Eq.any_n = Eq[-1].this.limits[0][1].definition

    p_quote = Symbol(Eq.deduction.expr.expr.lhs)
    Eq.p_quote_definition = p_quote.this.definition

    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)

    Eq << Eq.p_quote_definition.lhs[n].this.definition

    Eq << Eq[-1].this.rhs.args[1].expr.apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << algebra.all_any_eq.cond.then.all.any.subs.apply(Eq.any_n, Eq[-1])

    Eq << Eq[-1].this.expr().expr.rhs.simplify()

    Eq.any_n_plausible = Eq[-1].this.expr.apply(sets.any.then.any.limits.relax, wrt=Eq[-1].expr.variable)

    Eq << discrete.then.all_el.permutation.apply(n + 1, left=False)

    i, j = Eq[-1].find(Indexed).indices
    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.any_n_plausible.variable).subs(Eq.p_quote_definition.reversed)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.limits[0][1].definition

    Eq <<= Eq.any_n_plausible & Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.cond.any.then.any.et)

    Eq << Eq[-1].this.expr.expr.apply(discrete.eq.eq.then.eq.permutation.pop.interval)

    Eq << algebra.all.then.ou.subs.apply(Eq.hypothesis, Eq.hypothesis.variable, p_quote[:n])

    Eq << algebra.cond.all.then.all.et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(algebra.any.ou.then.cond, simplify=None)

    Eq << Eq.p_quote_definition.lhs.this.apply(algebra.expr.to.block, n)

    Eq << algebra.cond.all_any.then.all.any.et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(algebra.eq.eq.then.eq.subs, swap=True)

    Eq <<= Eq[-1] & Eq.any_n_plausible

    Eq << Eq[-1].this.expr.apply(algebra.any.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(algebra.eq.eq.then.eq.subs, swap=True)

    Eq << Eq[-1].this.find(Any).apply(algebra.any.limits.concat)
    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.infer.then.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)

    Eq << Eq[1].subs(Eq[0])





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-01
# updated on 2023-11-18
