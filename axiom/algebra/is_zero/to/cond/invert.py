from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Equal[Bool])
    return cond.invert()


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(Equal(Bool(a > b), 0))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.is_zero.imply.cond.invert)

    Eq << Eq[-1].this.rhs.apply(algebra.is_zero.given.cond.invert)

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
