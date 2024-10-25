from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(Bool(a > b) > 0)

    Eq << Eq[0].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << algebra.cond_piece.of.et.infer.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-11-05
