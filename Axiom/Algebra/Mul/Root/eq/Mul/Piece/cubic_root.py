from util import *


@apply
def apply(self):
    A, B = self.of(Mul)
    A = A.of(Expr ** (S.One / 3))
    B = B.of(Expr ** (S.One / 3))
    C = (A * B) ** (S.One / 3)
    d = Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    return Equal(self, C * Piecewise((1, Equal(A, 0) | Equal(B, 0) | Equal(d, 0)), (w, Arg(A) + Arg(B) > S.Pi), (~w, True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(A ** (S.One / 3) * B ** (S.One / 3) )

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Equal(A, 0) | Equal(B, 0))

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2])

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[2], invert=True)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Eq[-1].find(ExprCondPair[~Equal]))

    Eq <<= Algebra.Imply.of.Imply.subs.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.lhs.apply(Algebra.Ne_.Ceiling.Zero.to.Or_Eq.Arg)

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne_0.Ne_0.Eq.to.Eq.cubic_root)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_Arg.equ.Eq_Ceiling, simplify=None)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply.of.Imply.subs.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)
    Eq <<= Eq[-2].this.lhs.apply(Algebra.Ne_0.Ne_0.Eq.to.Eq.cubic_root)
    Eq <<= Eq[-1].this.lhs.apply(Algebra.Ne_0.Ne_0.Eq.to.Eq.cubic_root)


if __name__ == '__main__':
    run()
# created on 2018-11-01
