from util import *


def is_differentiable_at(cond, dir=1):
    (dfx, domain), (x, a, b) = cond.of(All[Element])
    fx, (S[x + dir * S.Infinitesimal], S[1]) = dfx.of(Derivative)
    assert domain in Interval(-oo, oo, left_open=False, right_open=False)
    return fx, (x, a, b)

@apply
def apply(lt, is_continuous, left_is_real, right_is_real, equal):
    a, b = lt.of(Less)
    from Axiom.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_continuous
    fx, (x, S[a], S[b]) = of_continuous(is_continuous)
    S[fx], S[(x, a, b)] = is_differentiable_at(left_is_real)
    S[fx], S[(x, a, b)] = is_differentiable_at(right_is_real, -1)

    S[fx._subs(x, a)], S[fx._subs(x, b)] = equal.of(Equal)

    return Any[x:a:b](Derivative[x - S.Infinitesimal](fx) * Derivative[x + S.Infinitesimal](fx) <= 0)


@prove
def prove(Eq):
    from Axiom import Calculus, Set, Algebra, Logic

    a, b, x = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Axiom.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        a < b,
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        Equal(f(a), f(b)))

    Eq << Eq[2].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Eq[3].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Set.Subset.Finset.of.Lt.apply(Eq[0], simplify=None)

    Eq.eq_intersect = Set.EqInter.of.Subset.apply(Eq[-1])

    ξ = Eq[1].variable
    c0, c1 = Symbol(real=True)
    Eq << Calculus.Any.All.Ge.of.Lt.IsContinuous.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c0)

    # Eq << Eq[-1].this.expr.expr.reversed
    Eq << Algebra.Or.Any.of.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Calculus.Any.All.Le.of.Lt.IsContinuous.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c1)

    Eq << Algebra.Or.Any.of.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.apply(Logic.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.find(And[Or]).apply(Logic.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.Any.And.of.Any.Any)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.of.And, 1)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.of.And)

    Eq << Logic.Cond.given.And.Imp.apply(Eq[5], cond=Eq[-1])

    Eq.any_max, Eq.any_min, Eq.any_boundary = Logic.ImpOr.given.Imp.Imp.apply(Eq[-1], None)

    Eq <<= Eq.any_min.this.lhs.apply(Algebra.Any.And.of.Any.limits.unleash, simplify=None), \
        Eq.any_max.this.lhs.apply(Algebra.Any.And.of.Any.limits.unleash, simplify=None)

    Eq <<= Eq[1] & Eq[2] & Eq[3]

    Eq <<= Logic.Imp.given.And.Imp.invert.apply(Eq[-3], cond=Eq[-1]), Logic.Imp.given.And.Imp.invert.apply(Eq[-2], cond=Eq[-1])

    Eq <<= Logic.Or.given.Cond.apply(Eq[-3], 0), Logic.Or.given.Cond.apply(Eq[-1], 0)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(Algebra.Any.And.of.Cond.Any, simplify=None), \
        Eq[-2].this.lhs.args[:2].apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq <<= Eq[-2].this.lhs.args[:2].apply(Algebra.Any.And.of.Cond.Any, simplify=None), \
        Eq[-1].this.lhs.args[:2].apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq.Any_And_min = Eq[-2].this.lhs.apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq.Any_And_max = Eq[-1].this.lhs.apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    et = And(*Eq.Any_And_max.lhs.expr.args)
    Eq <<= et.this.apply(Logic.Cond.of.And, slice(0, 4)), et.this.apply(Logic.Cond.of.And, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[LessEqual]).apply(Algebra.All.of.All.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[LessEqual]).apply(Algebra.All.of.All.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Le_0.Subs.Grad.of.Mem_Icc.IsContinuous.IsExtendedReal.All_Le), Eq[-1].this.rhs.apply(Calculus.Ge_0.Subs.Grad.of.Mem_Icc.IsContinuous.IsExtendedReal.All_Le)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.of.Le_0.Ge_0)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1], 0)

    Eq << Logic.Imp.Any.of.Imp.apply(Eq[-1], c1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Any_And.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c1, x)

    et = And(*Eq.Any_And_min.lhs.expr.args)
    Eq <<= et.this.apply(Logic.Cond.of.And, slice(0, 4)), et.this.apply(Logic.Cond.of.And, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[GreaterEqual]).apply(Algebra.All.of.All.limits.restrict, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[GreaterEqual]).apply(Algebra.All.of.All.limits.restrict, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Ge_0.Subs.Grad.of.Mem_Icc.IsContinuous.IsExtendedReal.All_Ge), Eq[-1].this.rhs.apply(Calculus.Le_0.Subs.Grad.of.Mem_Icc.IsContinuous.IsExtendedReal.All_Ge)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.of.Le_0.Ge_0)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1], 0)

    Eq << Logic.Imp.Any.of.Imp.apply(Eq[-1], c0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Any_And.limits_absorb, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c0, x)

    Eq << Eq.any_boundary.this.lhs.apply(Algebra.Any.And.of.Any.limits.unleash, simplify=None)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[4], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq << Eq[-1].this.find(And).args[:-1].apply(Set.Eq.of.Mem_Finset.Mem_Finset.Eq)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.of.Le.Ge)

    Eq << Eq[-1].this.find(Equal).apply(Calculus.EqGrad.of.Eq, (x,))

    Eq << Eq[-1].this.find(Equal).rhs.doit()

    Eq << Eq[-1].this.find(Equal).apply(Calculus.And.Eq_Grad.of.Eq_Grad)

    Eq << Eq[-1].this.find(And).apply(Algebra.EqMul.of.Eq.Eq)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Le.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.restrict, Interval.open(a, b))

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subs, x, (a + b) / 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.of.All.subs, x, (a + b) / 2)

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << Set.Mem.Icc.of.Lt.average.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-10-14
# updated on 2023-11-10
0
