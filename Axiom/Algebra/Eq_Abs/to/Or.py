from util import *


@apply
def apply(given):
    abs_x, y = given.of(Equal)
    if not abs_x.is_Abs:
        abs_x, y = y, abs_x

    x = abs_x.of(Abs)
    assert x.is_real

    return Or(Equal(x, y), Equal(x, -y))


@prove
def prove(Eq):
    from Axiom import Algebra
    x, a = Symbol(real=True, given=True)
    Eq << apply(Equal(abs(x), a))

    Eq << Eq[0].this.lhs.apply(Algebra.Abs.eq.Piece)

    Eq << Algebra.Cond_Piece.to.Or.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Algebra.And.to.Or.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2019-04-21