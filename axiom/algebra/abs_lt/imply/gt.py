from util import *


@apply
def apply(given, negate=None):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    if negate:
        x = -x
    assert x.is_extended_real
    return Greater(x, -a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << algebra.imply.le.abs.apply(-x)

    Eq << -Eq[-1]

    Eq << -Eq[0]

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[-2], Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2018-07-27
# updated on 2023-04-16
