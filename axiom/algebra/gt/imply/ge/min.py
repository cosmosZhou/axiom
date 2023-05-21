from util import *


@apply
def apply(given, m):
    lhs, rhs = given.of(Greater)
    return GreaterEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, z = Symbol(real=True, given=True)

    Eq << apply(x > y, z)
    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << algebra.ge.imply.ge.min.apply(Eq[-1], z)

if __name__ == '__main__':
    run()
# created on 2019-07-22
