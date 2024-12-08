from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    M, S[x] = le.of(LessEqual)

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x <= 0, M <= x)

    Eq << Algebra.Le.Le.to.Le.trans.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << Algebra.Le.Ge.to.Ge.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Le.Ge.to.Le_0.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]




if __name__ == '__main__':
    run()
# created on 2019-12-07
# updated on 2023-05-20
