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
    from Axiom import Algebra, Sets, Discrete

    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(n)

    b = Eq[1].expr.variable.base
    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.doit(deep=True)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    p0 = Eq[-1].variable
    Eq << Eq[-1].this.expr.apply(Algebra.Any.of.Cond.subs, b[:2], Matrix((0, KroneckerDelta(p0, 0))))

    Eq << Eq[-1].this.expr.rhs.expand()

    Eq << Eq[-1].this.expr.rhs[0].simplify()

    Eq.equation = Eq[-1].this.expr.rhs[1].simplify()

    Eq.limits_assertion = Algebra.All.limits_assert.apply(Eq.equation.limits)

    Eq << Eq.limits_assertion.this.expr.apply(Sets.Eq.to.Eq.split.FiniteSet.Add)

    Eq.p1_equality = Eq[-1].this.expr - p0

    Eq <<= Eq.equation & Eq.p1_equality

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.of.And.split.Matrix)

    Eq.premier, Eq.second = Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Eq.limits_assertion.this.expr.apply(Sets.Eq.to.And.split.FiniteSet)

    Eq << Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(Sets.In.to.Eq.Delta.Zero).reversed

    Eq << -(Eq.premier - 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.expr.expr.rhs.args[1].this.apply(Discrete.MatProd.eq.Dot.pop)

    Eq << Discrete.Block.eq.MatProd.apply(n, n, b)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(Algebra.Lamda.eq.Block.pop)

    Eq << MatMul(*Eq[-1].expr.expr.rhs.args[:2]).this.apply(Discrete.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.deduction = Eq[-1].this.expr.expr @ Eq[-1].expr.expr.rhs.args[1]

    Eq << Discrete.All_Any_Eq.permutation.basic.apply(n + 1)

    Eq << Eq[-1].this.expr.limits_subs(Eq[-1].expr.variable, b[n])

    Eq.any_n = Eq[-1].this.limits[0][1].definition

    p_quote = Symbol(Eq.deduction.expr.expr.lhs)
    Eq.p_quote_definition = p_quote.this.definition

    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)

    Eq << Eq.p_quote_definition.lhs[n].this.definition

    Eq << Eq[-1].this.rhs.args[1].expr.apply(Algebra.Piece.eq.Delta)

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Sum)

    Eq << Algebra.All_Any_Eq.Cond.to.All.Any.subs.apply(Eq.any_n, Eq[-1])

    Eq << Eq[-1].this.expr().expr.rhs.simplify()

    Eq.any_n_plausible = Eq[-1].this.expr.apply(Sets.Any.to.Any.limits.relax, wrt=Eq[-1].expr.variable)

    Eq << Discrete.All_InDot.permutation.apply(n + 1, left=False)

    i, j = Eq[-1].find(Indexed).indices
    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.any_n_plausible.variable).subs(Eq.p_quote_definition.reversed)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.limits[0][1].definition

    Eq <<= Eq.any_n_plausible & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Any.to.Any.And)

    Eq << Eq[-1].this.expr.expr.apply(Discrete.Eq.Eq.to.Eq.permutation.pop.Interval)

    Eq << Algebra.All.to.Or.subs.apply(Eq.hypothesis, Eq.hypothesis.variable, p_quote[:n])

    Eq << Algebra.Cond.All.to.All.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Algebra.Any.Or.to.Cond, simplify=None)

    Eq << Eq.p_quote_definition.lhs.this.apply(Algebra.Expr.eq.Block, n)

    Eq << Algebra.Cond.All_Any.to.All.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True)

    Eq <<= Eq[-1] & Eq.any_n_plausible

    Eq << Eq[-1].this.expr.apply(Algebra.Any.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True)

    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.limits.concat)
    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)

    Eq << Eq[1].subs(Eq[0])





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-01
# updated on 2023-11-18