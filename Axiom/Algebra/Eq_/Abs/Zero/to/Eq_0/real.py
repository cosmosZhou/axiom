from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << Eq[0].this.lhs.apply(Algebra.Abs.eq.Piece)

    Eq << Algebra.Cond_Piece.to.Or.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-03-15