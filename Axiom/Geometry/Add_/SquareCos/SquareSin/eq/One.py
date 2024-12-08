from util import *


@apply
def apply(x):
    return Equal(cos(x) ** 2 + sin(x) ** 2, 1)


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Eq[0].this.find(Expr ** 2).apply(Geometry.Square.Sin.eq.Sub.Square.Cos)




if __name__ == '__main__':
    run()
# created on 2023-10-03
