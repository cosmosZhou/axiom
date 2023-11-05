from util import *


@apply
def apply(given):
    args = given.of(Mul > 0)
    args = [arg for arg in args if not arg > 0]
    return Mul(*args) > 0


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x * a > 0)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.gt_zero.imply.gt_zero.mul, 1 / a)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.imply.gt_zero.mul, a)


if __name__ == '__main__':
    run()
# created on 2023-11-05
