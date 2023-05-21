from util import *


@apply
def apply(self):
    x, y = self.of(Mul >= 0)
    return Or(And(x >= 0, y >= 0), And(x <= 0, y <= 0))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y >= 0)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge_zero.imply.ou.split.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.given.ou.split.mul)


if __name__ == '__main__':
    run()
# created on 2023-04-18
