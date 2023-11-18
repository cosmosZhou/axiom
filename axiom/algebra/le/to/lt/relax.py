from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_integer
    return Less(lhs, rhs + 1)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    Eq << apply(x <= y)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.le.imply.lt.relax)

    Eq << Eq[-1].this.rhs.apply(algebra.le.given.lt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
