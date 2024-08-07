from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert not domain.left_open
    return All[x:Interval(a, b, right_open=domain.right_open)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, calculus, sets

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b, right_open=True)
    x, t, e = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=t < b)

    Eq << algebra.infer_et.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.lt.all.imply.all.limits.restrict)

    Eq << Eq[-1].this.rhs.apply(calculus.all_ge_zero.imply.all.ge.monotony.right_close)

    Eq << Eq[-1].subs(t, b - e)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << -Eq[-1].this.lhs

    Eq.suffice = Eq[-1].this.rhs.apply(algebra.all.limits.subs.negate.real, x, b - x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(algebra.any.limits.subs.negate.real, x, b - x)

    Eq << algebra.any.imply.any.et.limits.cond.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.imply.gt)

    η = Symbol(real=True, positive=True)
    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.imply.any.gt, var=η)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.any.imply.any.et, simplify=None)

    Eq << algebra.any.imply.any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 1)

    Eq << Eq.suffice.subs(e, η)

    Eq << algebra.all.any.imply.any.et.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-10-03
