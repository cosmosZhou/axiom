from util import *


@apply
def apply(ge_0, ge_1):
    x, a = ge_0.of(GreaterEqual)
    y, b = ge_1.of(GreaterEqual)
    return GreaterEqual(Min(x, y), Min(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= a, y >= b)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Piece)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_Min.apply(a, b)

    Eq << Algebra.Ge.Ge.to.Ge.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    Eq << Algebra.Ge_Min.apply(b, a)

    Eq << Algebra.Ge.Ge.to.Ge.trans.apply(Eq[1], Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-1], Eq[-3], invert=True)





if __name__ == '__main__':
    run()
# created on 2019-05-17
# updated on 2023-04-29
