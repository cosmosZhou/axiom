from util import *


@apply
def apply(self):
    x = self.of(csch ** 2)
    return Equal(self, coth(x) ** 2 - 1)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x = Symbol(real=True)
    Eq << apply(csch(x) ** 2)

    Eq << Eq[0].this.find(coth).apply(Geometry.Coth.eq.Div)

    Eq << Eq[-1].this.find(cosh ** 2).apply(Geometry.Square.Cosh.eq.Add.Square.Sinh)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(sinh).apply(Geometry.Sinh.eq.Inv.Csch)




if __name__ == '__main__':
    run()
# created on 2023-11-26
