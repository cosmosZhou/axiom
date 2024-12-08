from util import *


@apply
def apply(self):
    x, y = self.of(Cos * Cos)
    return Equal(self, (cos(x + y) + cos(x - y)) / 2)


@prove
def prove(Eq):
    from Axiom import Geometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x) * cos(y))

    Eq << Eq[-1].this.find(Cos[Expr - Expr]).apply(Geometry.Cos.eq.Add)

    Eq << Eq[-1].this.find(Cos[Expr + Expr]).apply(Geometry.Cos.eq.Sub)


if __name__ == '__main__':
    run()
# created on 2023-06-01
