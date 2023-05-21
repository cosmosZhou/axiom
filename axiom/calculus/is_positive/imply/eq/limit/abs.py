from util import *


@apply
def apply(is_positive):
    limit, R = is_positive.of(Element)
    (fx, *limits) = limit.of(Limit)
    assert R in Interval(0, oo, left_open=True)
    return Equal(Limit(abs(fx), *limits), limit)


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Interval(0, oo, left_open=True)))

    Eq << sets.el.imply.eq.definition.apply(Eq[0], 'y')

    y = Eq[-1].lhs
    δ_0 = Symbol(positive=True)
    Eq <<= calculus.eq_limit.imply.any.all.limit_definition.apply(Eq[-1], delta=δ_0), Eq[1].subs(Eq[-1].reversed)

    δ = Symbol(positive=True)
    Eq << calculus.eq_limit.given.any_all.limit_definition.apply(Eq[-1], delta=δ)

    Eq << Greater(y, 0, plausible=True)

    δ_1 = Symbol(positive=True)
    Eq << calculus.gt_zero.eq_limit.imply.any.all.gt.apply(Eq[-1], Eq[2], delta=δ_1)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.imply.gt.relax, 0)

    Eq << algebra.any_all.any_all.imply.any.all.et.limits_intersect.apply(Eq[-1], Eq[3])

    Eq << Eq[-1].this.find(Less & Less).args[:2].apply(algebra.lt.lt.given.lt.min)

    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.imply.eq.abs)

    Eq << Eq[-1].this.find(And).apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-04-18
