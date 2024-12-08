from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr > 0)
    return sin(x) <= x

@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << Algebra.Gt.to.Ge.relax.apply(Eq[0])

    Eq << Geometry.Ge_0.to.LeSin.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
