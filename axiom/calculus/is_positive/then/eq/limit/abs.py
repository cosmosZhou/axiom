from util import *


@apply
def apply(is_positive):
    limit, R = is_positive.of(Element)
    (fx, *limits) = limit.of(Limit)
    assert R in Interval.open(0, oo)
    return Equal(Limit(abs(fx), *limits), limit)


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Interval.open(0, oo)))

    Eq << sets.el.then.eq.definition.apply(Eq[0], 'y')

    y = Eq[-1].lhs
    δ_0 = Symbol(positive=True)
    Eq <<= calculus.eq_limit.then.any.all.limit_definition.apply(Eq[-1], delta=δ_0), Eq[1].subs(Eq[-1].reversed)

    δ = Symbol(positive=True)
    Eq << calculus.eq_limit.of.any_all.limit_definition.apply(Eq[-1], delta=δ)

    Eq << Greater(y, 0, plausible=True)

    δ_1 = Symbol(positive=True)
    Eq << calculus.gt_zero.eq_limit.then.any.all.gt.apply(Eq[-1], Eq[2], delta=δ_1)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.then.gt.relax, 0)

    Eq << algebra.any_all.any_all.then.any.all.et.limits_intersect.apply(Eq[-1], Eq[3])

    Eq << Eq[-1].this.find(Less & Less).args[:2].apply(algebra.lt.lt.of.lt.min)

    Eq << algebra.any.then.any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.then.eq.abs)

    Eq << Eq[-1].this.find(And).apply(algebra.eq.cond.then.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-04-18
