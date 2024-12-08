from util import *


@apply
def apply(self):
    x = self.of(Sinh ** 2)
    return Equal(self, cosh(x) ** 2 - 1)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x = Symbol(real=True)
    Eq << apply(sinh(x) ** 2)

    Eq << Eq[-1].this.find(sinh).apply(Geometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.lhs.apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.find(cosh).apply(Geometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Square.eq.Add)


if __name__ == '__main__':
    run()
# created on 2023-11-26
