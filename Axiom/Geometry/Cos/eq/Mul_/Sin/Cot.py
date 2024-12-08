from util import *


@apply
def apply(x):
    return Equal(cos(x), cot(x) * sin(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0].this.find(cot).apply(Geometry.Cot.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-10-03
