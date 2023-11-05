from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(Bool(a > b) > 0)

    

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.gt_zero.imply.cond)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.given.cond)

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
