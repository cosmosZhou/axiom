from util import *


@apply
def apply(given, swap=False):
    (a, b), M = given.of(Abs[Expr - Expr] < Expr)
#     |a - b| < M
    if swap:
        a, b = b, a
    return Less(abs(a), Max(abs(M + b), abs(M - b)))


@prove
def prove(Eq):
    from Axiom import Algebra
    M, a, b = Symbol(real=True)

    Eq << apply(Less(abs(a - b), M))

    Eq << Algebra.Lt.to.Lt.split.Abs.apply(Eq[0]) + b

    Eq << Algebra.Le_Abs.apply(M + b)

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[-2], Eq[-1])

    Eq << LessEqual(abs(M + b), Eq[1].rhs, plausible=True)

    Eq.strict_less_than = Algebra.Lt.Le.to.Lt.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt.to.Lt.split.Abs.apply(Eq[0], negate=True) - b

    Eq << Algebra.Le_Abs.apply(M - b)

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[-2], Eq[-1])

    Eq << LessEqual(abs(M - b), Eq[1].rhs, plausible=True)

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt.Lt.to.Lt.Abs.apply(Eq.strict_less_than, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-12-30
