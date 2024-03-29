from util import *


@apply
def apply(given):
    fx, (x, S[1]) = given.of(Derivative > 0)
    domain = x.domain
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b))
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x)) > 0)

    Eq << algebra.cond.imply.all.apply(Eq[0], x)

    Eq << calculus.all_gt_zero.imply.all.gt.monotony.right_close.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-06-02
