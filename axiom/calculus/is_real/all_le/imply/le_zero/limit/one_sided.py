from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    x0, epsilon = x0.clear_infinitesimal()
    assert epsilon
    assert R in Reals
    S[fx], (x, *cond) = all_le.of(All[Expr <= 0])
    if epsilon > 0:
        S[x0], delta = cond
        delta -= x0
        assert delta > 0
    else:
        delta, S[x0] = cond
        delta -= x0
        assert delta < 0
        
    return lim <= 0


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals),
        All[x:x0:x0 + delta](f(x) <= 0))

    Eq << ~Eq[2]

    A = Symbol(Eq[-1].lhs)
    Eq << A.this.definition.reversed

    Eq << Eq[-2].subs(Eq[-1])

    δ_quote = Symbol(real=True, positive=True)
    Eq << calculus.gt_zero.eq_limit.imply.any.all.gt.apply(*Eq[-2:], delta=δ_quote)

    Eq << algebra.cond.any_all.imply.any.all.et.apply(Eq[-2] / 2, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(algebra.gt.gt.imply.gt.transit)

    Eq << Eq[-1].this.find(All).apply(algebra.all.imply.all.limits.restrict, domain=Interval.open(x0, x0 + Min(δ_quote, delta)))

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], domain=Interval.open(x0, x0 + Min(δ_quote, delta)))

    Eq << algebra.cond.any.imply.any.et.apply(*Eq[-2:], simplify=None)

    

    


if __name__ == '__main__':
    run()
# created on 2023-10-15
