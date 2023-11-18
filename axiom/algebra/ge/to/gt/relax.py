from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert lhs.is_integer
    return Greater(lhs, rhs - 1)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    Eq << apply(x >= y)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge.imply.gt.relax)

    Eq << Eq[-1].this.rhs.apply(algebra.ge.given.gt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
