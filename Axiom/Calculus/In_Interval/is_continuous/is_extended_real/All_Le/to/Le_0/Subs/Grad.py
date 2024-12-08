from util import *


@apply
def apply(el_Interval, is_continuous, is_extended_real, all_le):
    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from Axiom.Calculus.Lt.is_continuous.is_extended_real.is_extended_real.Eq.to.Any.Le.Rolle import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real)

    c, S[Interval.open(a, b)] = el_Interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_le.of(All[LessEqual])
    return Subs[x:c](Derivative[x + S.Infinitesimal](fx)) <= 0


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) <= f(c)))

    Eq <<= Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided), Algebra.All.to.All.limits.subs.offset.apply(Eq[-2], c)

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Sets.In.to.In.Sub.apply(Eq[0], c)

    Eq.gt_zero = Sets.In_Interval.to.Lt.apply(Eq[-1]).this.apply(Algebra.Lt.to.Gt_0)

    Eq << Algebra.Cond.Imply.to.Imply.And.lhs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Sets.In.In.of.And.In)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.to.Le_0)

    Eq << Algebra.Imply.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.is_positive.Le.to.Le.Div)

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Sets.Gt_0.to.is_positive.apply(Eq.gt_zero, simplify=None)

    δ = Symbol(real=True, positive=True)
    Eq << Sets.In.to.Any.Eq.apply(Eq[-1], var=δ)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-3], Eq[-1], simplify=None)

    Eq.Any_All = Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Algebra.All.to.Imply.apply(Eq[2])

    Eq << Eq[-1].subs(x, c)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided, simplify=2)

    Eq << Eq.Any_All.this.find(All).limits_subs(x, Eq[-1].lhs.variable)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.Any_All, simplify=None)

    Eq << Eq[-1].this.expr.apply(Calculus.is_extended_real.All_Le.to.Le_0.Limit.one_sided)




if __name__ == '__main__':
    run()
# created on 2023-10-15
