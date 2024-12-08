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

    Eq << Eq[0].this.find(Bool).apply(Algebra.Bool.eq.Piece)




if __name__ == '__main__':
    run()
# created on 2023-11-05
