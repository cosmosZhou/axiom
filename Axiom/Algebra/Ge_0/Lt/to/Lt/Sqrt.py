from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x < M)

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[0], Eq[1])

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[0])

    Eq << Algebra.Gt.Ge.to.Gt.Add.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt.to.Lt_0.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Algebra.Gt_0.Lt.to.Lt.Div.apply(Eq[-3], Eq[-1])

    Eq << Algebra.Lt_0.to.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-28