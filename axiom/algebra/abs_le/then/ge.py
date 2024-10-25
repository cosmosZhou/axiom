from util import *


@apply
def apply(given, negate=False):
    x, M = given.of(LessEqual)
    x = x.of(Abs)
    if negate:
        x = -x
    assert x.is_extended_real
    return GreaterEqual(x, -M)


@prove
def prove(Eq):
    from axiom import algebra

    M, a = Symbol(real=True)
    Eq << apply(LessEqual(abs(a), M), negate=True)

    Eq << algebra.then.le.abs.apply(a)

    Eq << algebra.le.le.then.le.trans.apply(Eq[-1], Eq[0])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-04-16
