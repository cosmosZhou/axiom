from util import *


@apply
def apply(cosx):
    i = S.ImaginaryUnit
    x = cosx.of(Cos)
    return Equal(cosx, Re(E ** (i * x), evaluate=False))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[0].this.find(Exp).apply(Geometry.ExpMulI.eq.AddCos_MulISin.Euler)


if __name__ == '__main__':
    run()
# created on 2023-06-03
