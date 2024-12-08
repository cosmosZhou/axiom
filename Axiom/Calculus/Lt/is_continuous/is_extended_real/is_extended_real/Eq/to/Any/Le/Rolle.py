from util import *


def is_differentiable_at(cond, dir=1):
    (dfx, domain), (x, a, b) = cond.of(All[Element])
    fx, (S[x + dir * S.Infinitesimal], S[1]) = dfx.of(Derivative)
    assert domain in Interval(-oo, oo, left_open=False, right_open=False)
    return fx, (x, a, b)

@apply
def apply(lt, is_continuous, left_is_real, right_is_real, equal):
    a, b = lt.of(Less)
    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import of_continuous
    fx, (x, S[a], S[b]) = of_continuous(is_continuous)
    S[fx], S[(x, a, b)] = is_differentiable_at(left_is_real)
    S[fx], S[(x, a, b)] = is_differentiable_at(right_is_real, -1)

    S[fx._subs(x, a)], S[fx._subs(x, b)] = equal.of(Equal)

    return Any[x:a:b](Derivative[x - S.Infinitesimal](fx) * Derivative[x + S.Infinitesimal](fx) <= 0)


@prove
def prove(Eq):
    from Axiom import Calculus, Sets, Algebra

    a, b, x = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        a < b,
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        Equal(f(a), f(b)))

    Eq << Eq[2].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Eq[3].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Sets.Lt.to.Subset.FiniteSet.apply(Eq[0], simplify=None)

    Eq.eq_intersect = Sets.Subset.to.Eq.Intersect.apply(Eq[-1])

    ξ = Eq[1].variable
    c0, c1 = Symbol(real=True)
    Eq << Calculus.Lt.is_continuous.to.Any.All.Ge.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c0)

    # Eq << Eq[-1].this.expr.expr.reversed
    Eq << Algebra.Any.to.Or.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Calculus.Lt.is_continuous.to.Any.All.Le.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c1)

    Eq << Algebra.Any.to.Or.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.find(And[Or]).apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.Any.Any.to.Any.And)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.to.Cond, 1)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.to.Cond)

    Eq << Algebra.Cond.of.And.Imply.apply(Eq[5], cond=Eq[-1])

    Eq.any_max, Eq.any_min, Eq.any_boundary = Algebra.Imply_Or.of.And.Imply.apply(Eq[-1], None)

    Eq <<= Eq.any_min.this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None), \
        Eq.any_max.this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None)

    Eq <<= Eq[1] & Eq[2] & Eq[3]

    Eq <<= Algebra.Imply.of.And.Imply.invert.apply(Eq[-3], cond=Eq[-1]), Algebra.Imply.of.And.Imply.invert.apply(Eq[-2], cond=Eq[-1])

    Eq <<= Algebra.Or.of.Cond.apply(Eq[-3], 0), Algebra.Or.of.Cond.apply(Eq[-1], 0)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(Algebra.Cond.Any.to.Any.And, simplify=None), \
        Eq[-2].this.lhs.args[:2].apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq <<= Eq[-2].this.lhs.args[:2].apply(Algebra.Cond.Any.to.Any.And, simplify=None), \
        Eq[-1].this.lhs.args[:2].apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq.Any_And_min = Eq[-2].this.lhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq.Any_And_max = Eq[-1].this.lhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    et = And(*Eq.Any_And_max.lhs.expr.args)
    Eq <<= et.this.apply(Algebra.And.to.Cond, slice(0, 4)), et.this.apply(Algebra.And.to.Cond, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[LessEqual]).apply(Algebra.All.to.All.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[LessEqual]).apply(Algebra.All.to.All.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.In_Interval.is_continuous.is_extended_real.All_Le.to.Le_0.Subs.Grad), Eq[-1].this.rhs.apply(Calculus.In_Interval.is_continuous.is_extended_real.All_Le.to.Ge_0.Subs.Grad)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.Ge_0.to.Le_0)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1], 0)

    Eq << Algebra.Imply.to.Imply.Any.apply(Eq[-1], c1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any_And.to.Any.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c1, x)

    et = And(*Eq.Any_And_min.lhs.expr.args)
    Eq <<= et.this.apply(Algebra.And.to.Cond, slice(0, 4)), et.this.apply(Algebra.And.to.Cond, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[GreaterEqual]).apply(Algebra.All.to.All.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[GreaterEqual]).apply(Algebra.All.to.All.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.In_Interval.is_continuous.is_extended_real.All_Ge.to.Ge_0.Subs.Grad), Eq[-1].this.rhs.apply(Calculus.In_Interval.is_continuous.is_extended_real.All_Ge.to.Le_0.Subs.Grad)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.Ge_0.to.Le_0)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1], 0)

    Eq << Algebra.Imply.to.Imply.Any.apply(Eq[-1], c0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any_And.to.Any.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c0, x)

    Eq << Eq.any_boundary.this.lhs.apply(Algebra.Any.to.Any.And.limits.unleash, simplify=None)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[4], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.find(And).args[:-1].apply(Sets.In_FiniteSet.In_FiniteSet.Eq.to.Eq)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Le.Ge.to.Eq)

    Eq << Eq[-1].this.find(Equal).apply(Calculus.Eq.to.Eq.Grad, (x,))

    Eq << Eq[-1].this.find(Equal).rhs.doit()

    Eq << Eq[-1].this.find(Equal).apply(Calculus.Eq_Grad.to.And.Eq_Grad)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.to.Eq.Mul)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq.to.Le)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.to.All.limits.restrict, Interval.open(a, b))

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Cond.subs, x, (a + b) / 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.to.Cond.subs, x, (a + b) / 2)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Sets.Lt.to.In.Interval.average.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-10-14
# updated on 2023-11-10
0
