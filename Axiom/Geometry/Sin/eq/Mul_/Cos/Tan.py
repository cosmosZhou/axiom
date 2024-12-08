from util import *


@apply
def apply(x):
    return Equal(sin(x), tan(x) * cos(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0].this.find(tan).apply(Geometry.Tan.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-10-03
