from util import *


@apply
def apply(is_positive):
    limit, R = is_positive.of(Element)
    (fx, *limits) = limit.of(Limit)
    assert R in Interval.open(0, oo)
    return Equal(Limit(abs(fx), *limits), limit)


@prove
def prove(Eq):
    from Axiom import Sets, Calculus, Algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Interval.open(0, oo)))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0], 'y')

    y = Eq[-1].lhs
    δ_0 = Symbol(positive=True)
    Eq <<= Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[-1], delta=δ_0), Eq[1].subs(Eq[-1].reversed)

    δ = Symbol(positive=True)
    Eq << Calculus.Eq_Limit.of.Any_All.limit_definition.apply(Eq[-1], delta=δ)

    Eq << Greater(y, 0, plausible=True)

    δ_1 = Symbol(positive=True)
    Eq << Calculus.Gt_0.Eq_Limit.to.Any.All.Gt.apply(Eq[-1], Eq[2], delta=δ_1)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Gt.relax, 0)

    Eq << Algebra.Any_All.Any_All.to.Any.All.And.limits_Intersect.apply(Eq[-1], Eq[3])

    Eq << Eq[-1].this.find(Less & Less).args[:2].apply(Algebra.Lt.Lt.of.Lt.Min)

    Eq << Algebra.Any.to.Any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.to.Eq.Abs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-04-18
