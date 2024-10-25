from util import *


@apply
def apply(is_positive):
    limit, R = is_positive.of(Element)
    (fx, *limits) = limit.of(Limit)
    assert R in Interval.open(-oo, 0)
    return Equal(Limit(abs(fx), *limits), -limit)


@prove
def prove(Eq):
    from axiom import calculus, sets

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Interval.open(-oo, 0)))

    @Function
    def f(x):
        return -g(x)
    Eq << f(x).this.defun()

    Eq << -Eq[-1].reversed

    Eq <<= Eq[0].subs(Eq[-1]), Eq[1].subs(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(calculus.limit.to.mul), Eq[-1].this.rhs.find(Limit).apply(calculus.limit.to.mul)

    Eq << sets.el.then.el.neg.apply(Eq[-2])

    Eq << calculus.is_positive.then.eq.limit.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
