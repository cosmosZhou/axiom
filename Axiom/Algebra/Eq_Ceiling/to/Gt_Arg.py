from util import *


@apply
def apply(eq):
    ((A, B), S[S.One / (S.Pi * 2)]), S[S.One / 2] = eq.of(Equal[Ceiling[(Arg + Arg) * Expr - Expr], 1])
    return Arg(A) + Arg(B) > S.Pi


@prove
def prove(Eq):
    from Axiom import Algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1))

    Eq << Algebra.Eq.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_.Ceiling.Zero.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Gt.apply(Eq[-1])
    Eq << Eq[-1] * S.Pi * 2


if __name__ == '__main__':
    run()
# created on 2018-10-31