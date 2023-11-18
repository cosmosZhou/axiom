from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Unequal[Bool])
    return cond


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(Unequal(Bool(a > b), 0))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ne_zero.imply.cond)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.given.cond)

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
