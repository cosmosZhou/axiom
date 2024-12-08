from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Less(x * x, M * M)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x < M)

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Lt.Gt.to.Lt_0.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]




if __name__ == '__main__':
    run()
# created on 2019-07-05
# updated on 2023-05-20
