from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Equal(sign(x), 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True)
    Eq << apply(x > 0)

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[0])

    Eq << Eq[1].lhs.this.apply(Algebra.Sign.eq.Piece.Abs)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Algebra.Cond_Piece.to.Imply.apply(Eq[-1], 1)

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-05-29
# updated on 2023-06-06
