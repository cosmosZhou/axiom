from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.all.et.limits_cond, simplify=None)

    Eq << (a >= b).this.apply(sets.ge.imply.is_empty.interval, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=a < b)

    Eq << algebra.infer_et.imply.infer.et.apply(Eq[-1])
    Eq << Eq[-1].this.rhs.apply(calculus.lt.all_gt_zero.imply.all_gt.monotony.right_close)


if __name__ == '__main__':
    run()
# created on 2020-04-23
