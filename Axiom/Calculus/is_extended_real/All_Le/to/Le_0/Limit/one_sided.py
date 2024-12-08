from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    x0, epsilon = x0.clear_infinitesimal()
    assert epsilon
    assert R in ExtendedReals
    S[fx], (x, *ab) = all_le.of(All[Expr <= 0])
    if epsilon > 0:
        S[x0], delta = ab
        delta -= x0
        assert delta > 0
    else:
        delta, S[x0] = ab
        delta -= x0
        assert delta < 0
    return lim <= 0


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Sets

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 + S.Infinitesimal](f(x)), ExtendedReals),
        All[x:x0:x0 + delta](f(x) <= 0))

    Eq.is_real, Eq.is_not_real = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals))

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq.is_real, cond=Eq[1])

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], -1)

    Eq << Eq[-2].this.lhs.apply(Calculus.is_real.All_Le.to.Le_0.Limit.one_sided)

    Eq.infer, Eq.le_infinity = Algebra.Imply.of.And.Imply.invert.apply(Eq.is_not_real, cond=Eq[0])

    Eq << Eq[0].simplify()

    Eq.ne_infinity = Unequal(Limit[x:x0 + S.Infinitesimal](f(x)), oo, plausible=True)

    Eq << ~Eq.ne_infinity

    δ_quote = Symbol(real=True, positive=True)
    Eq << Calculus.Eq_oo.to.Any.All.Gt_0.apply(Eq[-1], delta=δ_quote)

    Eq << Eq[-1].this.expr.apply(Algebra.All.to.All.limits.restrict, domain=Interval.open(x0, x0 + Min(delta, δ_quote)))

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[1], domain=Interval.open(x0, x0 + Min(delta, δ_quote)))

    Eq << Algebra.Cond.Any.to.Any.And.apply(*Eq[-2:])

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq.infer, cond=Eq.ne_infinity)

    Eq << Eq[-1].this.lhs.apply(Sets.Ne.In.to.In.Complement)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.to.Le_0)




if __name__ == '__main__':
    run()
# created on 2023-10-15
