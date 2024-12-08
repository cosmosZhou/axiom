from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    S[x], M = lt.of(Less)

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x < M)

    Eq << Algebra.Gt_0.to.Ge_0.apply(Eq[0])
    Eq << Algebra.Ge_0.Lt.to.Lt.Sqrt.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-09-12
