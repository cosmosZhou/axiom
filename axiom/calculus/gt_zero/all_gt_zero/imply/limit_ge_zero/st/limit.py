from util import *


@apply
def apply(is_positive, all_is_positive):
    (fx, (x, x0, dir)), (epsilon, domain) = all_is_positive.of(All[Limit > 0])
    _0, delta = domain.of(Interval)
    assert _0 == 0
    b = x0 + epsilon
    assert not b._has(epsilon)
    return GreaterEqual(Limit[x:b:-1](fx), 0)


@prove(proved=False)
def prove(Eq):
    b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True, continuous=Interval(-oo, b, right_open=True))
    epsilon, delta = Symbol(real=True)
    Eq << apply(delta > 0, All[epsilon:Interval(0, delta, left_open=True)](Limit[x:b - epsilon](f(x)) > 0))


if __name__ == '__main__':
    run()
# created on 2020-06-25
