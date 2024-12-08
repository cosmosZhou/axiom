from util import *


@apply
def apply(self):
    x = self.of(sech ** 2)
    return Equal(self, 1 - tanh(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x = Symbol(real=True)
    Eq << apply(sech(x) ** 2)

    Eq << Eq[0].this.find(tanh).apply(Geometry.Tanh.eq.Div)

    Eq << Eq[-1].this.find(sinh ** 2).apply(Geometry.Square.Sinh.eq.Sub.Square.Cosh)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(cosh).apply(Geometry.Cosh.eq.Inv.Sech)


if __name__ == '__main__':
    run()
# created on 2023-11-26
