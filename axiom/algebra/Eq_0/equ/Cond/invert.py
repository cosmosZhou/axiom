from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Equal[Bool])
    return cond.invert()


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True)
    Eq << apply(Equal(Bool(a > b), 0))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_0.to.Cond.invert)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_0.of.Cond.invert)




if __name__ == '__main__':
    run()
# created on 2023-11-05
