from util import *


@apply(simplify=False)
def apply(x):
    return Element(sin(x), Interval(-1, 1))


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Geometry.Add_.SquareCos.SquareSin.eq.One.apply(x)

    Eq << Algebra.Eq_Add.to.Le.bounded.apply(Eq[1])

    Eq << Eq[-1].this.apply(Sets.LeSquare.equ.In.Interval)


if __name__ == '__main__':
    run()
# created on 2023-10-03
