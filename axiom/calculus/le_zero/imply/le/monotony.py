from util import *


@apply
def apply(given):
    fx, (x, S[1]) = given.of(Derivative <= 0)
    domain = x.domain
    assert not domain.left_open
    a, b = domain.of(Interval)
    return LessEqual(fx, fx._subs(x, a))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True)

    x = Symbol(domain=Interval(a, b))

    f = Function(real=True)

    Eq << apply(Derivative[x](f(x)) <= 0)


if __name__ == '__main__':
    run()
# created on 2019-09-20
