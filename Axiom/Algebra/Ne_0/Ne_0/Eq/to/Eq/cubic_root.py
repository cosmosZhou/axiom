from util import *


@apply
def apply(is_nonzero_A, is_nonzero_B, eq):
    A = is_nonzero_A.of(Unequal[0])
    B = is_nonzero_B.of(Unequal[0])
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    eq.lhs.of(Ceiling[Expr - Expr])
    (((S[A], S[B]), S[S.One / (S.Pi * 2)]), S[S.One / 2]), d = eq.of(Equal[Ceiling[(Arg + Arg) * Expr - Expr]])
    if d == 0:
        factor = 1
    elif d % 3 == 1:
        factor = w
    else:
        factor = ~w

    return Equal(A ** (S.One / 3) * B ** (S.One / 3), (A * B) ** (S.One / 3) * factor)


@prove
def prove(Eq):
    from Axiom import Algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(A, 0), Unequal(B, 0), Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1))

    Eq << Eq[-1].this.lhs.args[0].base.apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Eq[-1].this.lhs.args[0].base.apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Eq[-1].this.find(Pow[~Mul]).apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Eq[-1].this.find(Abs[Mul]).apply(Algebra.Abs.eq.Mul)

    Eq << Algebra.Eq.of.Eq.Div.apply(Eq[-1], Mul(*Eq[-1].lhs.args[:2]))

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].rhs.find(Arg).this.apply(Algebra.Arg.Mul.eq.Piece)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0] & Eq[1], Eq[-1], invert=True)

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].arg.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Exp.eq.Mul)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Expr.eq.Add.complex)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add, deep=True)




if __name__ == '__main__':
    run()
# created on 2018-10-26
