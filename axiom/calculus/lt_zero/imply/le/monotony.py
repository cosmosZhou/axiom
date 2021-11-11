from util import *


@apply
def apply(given):
    fx, (x, n) = given.of(Derivative < 0)
    assert n == 1

    domain = x.domain

    assert not domain.left_open
    a, b = domain.of(Interval)

    return LessEqual(fx, fx._subs(x, a))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True)

    x = Symbol(domain=Interval(a, b))

    f = Function(real=True)

    Eq << apply(Derivative[x](f(x)) < 0)


if __name__ == '__main__':
    run()

# created on 2021-09-29
# updated on 2021-09-29
