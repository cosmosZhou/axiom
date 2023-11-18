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
    from axiom import algebra, calculus, sets

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 + S.Infinitesimal](f(x)), ExtendedReals),
        All[x:x0:x0 + delta](f(x) <= 0))

    Eq.is_real, Eq.is_not_real = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals))

    Eq << algebra.infer.given.et.infer.invert.apply(Eq.is_real, cond=Eq[1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], -1)

    Eq << Eq[-2].this.lhs.apply(calculus.is_real.all_le.imply.le_zero.limit.one_sided)

    Eq.infer, Eq.le_infinity = algebra.infer.given.et.infer.invert.apply(Eq.is_not_real, cond=Eq[0])

    Eq << Eq[0].simplify()

    Eq.ne_infinity = Unequal(Limit[x:x0 + S.Infinitesimal](f(x)), oo, plausible=True)

    Eq << ~Eq.ne_infinity

    δ_quote = Symbol(real=True, positive=True)
    Eq << calculus.is_infinite.imply.any.all.gt_zero.apply(Eq[-1], delta=δ_quote)

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.all.limits.restrict, domain=Interval.open(x0, x0 + Min(delta, δ_quote)))

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], domain=Interval.open(x0, x0 + Min(delta, δ_quote)))

    Eq << algebra.cond.any.imply.any.et.apply(*Eq[-2:])

    Eq << algebra.infer.given.et.infer.invert.apply(Eq.infer, cond=Eq.ne_infinity)

    Eq << Eq[-1].this.lhs.apply(sets.ne.el.imply.el.complement)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.imply.le_zero)

    


if __name__ == '__main__':
    run()
# created on 2023-10-15
