from util import *


@apply
def apply(is_positive, self):
    factor = is_positive.of(Expr > 0)
    args = self.of(Min)

    args = [arg * factor for arg in args]
    return Equal(Min(*args), self * factor)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, Min(x, y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Piece)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Min.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.eq.Mul)

    Eq.eq = Algebra.Eq.of.Eq.Div.apply(Eq[-1], r)

    Eq.equivalent = Iff(Eq[-1].find(LessEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << Algebra.Iff.of.And.apply(Eq.equivalent)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2]), Algebra.Given.of.Given_And.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Gt_0.Le.to.Le.Div), Eq[-1].this.rhs.apply(Algebra.Gt_0.Le.to.Le.Mul)

    Eq << Algebra.Cond.of.Cond.subs.Cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)


if __name__ == '__main__':
    run()
# created on 2019-08-16