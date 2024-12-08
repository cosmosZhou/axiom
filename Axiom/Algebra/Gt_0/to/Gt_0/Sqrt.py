from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(sqrt(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(Greater(x, 0))

    Eq << Algebra.Gt_0.to.Ge_0.apply(Eq[0])

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Ne_0.to.Ne_0.Sqrt.apply(Eq[-1])

    Eq << Algebra.Ne_0.Ge_0.to.Gt_0.apply(Eq[-1], Eq[-3])




if __name__ == '__main__':
    run()
# created on 2018-07-17
# updated on 2023-06-20
