from util import *


@apply
def apply(le, x):
    a, b = le.of(LessEqual)
    return Equal(clip(x, a, b), Max(Min(x, b), a))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(a <= b, x)

    Eq << Algebra.Le.to.Eq.Min.apply(Eq[0])

    Eq << Eq[0].reversed

    Eq << Eq[1].this.find(clip).defun()

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a <= x)

    Eq <<= Eq[-2].this.find(Min[~Max]).apply(Algebra.Max.eq.Piece.Lt), Eq[-1].this.find(Min[~Max]).apply(Algebra.Max.eq.Piece.Lt)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.lhs.reversed

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2], invert=True), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq_Max.of.Ge), Eq[-1].subs(Eq[2])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.GeMin.of.And.Ge), Eq[-1].this.rhs.apply(Algebra.Eq_Max.of.Ge)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt.to.Eq.Min)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-26
