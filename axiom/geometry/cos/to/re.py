from util import *


@apply
def apply(cosx):
    i = S.ImaginaryUnit
    x = cosx.of(Cos)
    return Equal(cosx, Re(E ** (i * x), evaluate=False))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[0].this.find(Exp).apply(geometry.expi.to.add.Euler)


if __name__ == '__main__':
    run()
# created on 2023-06-03
