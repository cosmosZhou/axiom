from util import *


@apply
def apply(self):
    x, y = self.of(Arg[Expr + ImaginaryUnit * Expr])
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(x, 0) & Equal(y, 0)),
                                 (asin(y / r), x >= 0),
                                 (S.Pi - asin(y / r), y >= 0),
                                 (-S.Pi - asin(y / r), True)))


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x, y = Symbol(real=True)
    Eq << apply(Arg(x + y * S.ImaginaryUnit))

    Eq << Eq[0].this.lhs.apply(Geometry.Arg.eq.Piece.Acos)

    Eq << Eq[-1].this.find(acos).apply(Geometry.Acos.eq.Piece.Asin)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.unnest, 1)

    Eq << Eq[-1].this.find(acos).apply(Geometry.Acos.eq.Piece.Asin)

    Eq << Eq[-1].this.find(-Piecewise).apply(Algebra.Mul.eq.Piece)

    Eq.eq = Eq[-1].this.lhs.apply(Algebra.Piece.And.invert)

    ou = Eq.eq.find(Or)
    Eq.equivalent = Iff(ou & (x / sqrt(x ** 2 + y ** 2) >= 0), (x >= 0) & ou, plausible=True)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq.equivalent)

    Eq <<= Eq[-2].this.find(Or).apply(Algebra.Or_Ne_0.to.Gt_.Sqrt.Zero), Eq[-1].this.find(Or).apply(Algebra.Or_Ne_0.to.Gt_.Sqrt.Zero)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Ge_0.Gt_0.to.Ge_0), Eq[-1].this.lhs.apply(Algebra.Gt_0.Ge.to.Ge.Div)

    Eq << Algebra.Cond.of.Cond.subs.Cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.invert.delete)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 0, 3)

    Eq << Algebra.Cond.of.Cond.subs.Cond.apply(Eq[-1], old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq.eq1 = Eq[-1].this.lhs.apply(Algebra.Piece.invert.delete, 0, 3)

    Eq.suffice = Imply(y >= 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge_0.to.Eq.Abs)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq.eq2 = Algebra.Imply.to.Eq.Piece.apply(Eq.suffice, Eq.eq1.lhs)

    Eq.suffice = Imply(y < 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), -asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Eq.Abs)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Piece.And.invert.apply(Eq.eq2.rhs, 1, 2)

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq.suffice, Eq[-1].rhs)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.eq2, Eq[-1])

    Eq << Eq.eq1.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 1, 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 2, 1)

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq.suffice, Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, 2)





if __name__ == '__main__':
    run()
# created on 2018-07-24
# updated on 2023-05-10
