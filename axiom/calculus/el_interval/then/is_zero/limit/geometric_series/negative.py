from util import *


@apply
def apply(el, n):
    x, domain = el.of(Element)
    S[-1], S[0] = domain.of(Interval)
    assert domain.left_open and domain.right_open
    return Equal(Limit[n:oo](x ** n), ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 0, left_open=True, right_open=True)), n)

    Eq << sets.el.then.el.neg.apply(Eq[0])

    Eq << sets.el_interval.then.lt.apply(Eq[0])

    Eq << algebra.lt_zero.then.eq.abs.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq.is_zero = calculus.el_interval.then.is_zero.limit.geometric_series.positive.apply(Eq[-1], n)

    Eq <<= algebra.then.ge.abs.apply(Eq[1].find(Pow)), algebra.then.le.abs.apply(Eq[1].find(Pow))

    Eq <<= calculus.ge.then.ge.limit.apply(Eq[-2], (n, oo)), calculus.le.then.le.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-2].this.rhs.apply(calculus.limit.to.mul)

    Eq <<= Eq[-2].subs(Eq.is_zero), Eq[-1].subs(Eq.is_zero)

    Eq << algebra.ge.le.then.eq.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-04-17
