from util import *


@apply
def apply(self):
    x = self.of(Sin ** 2)
    return Equal(self, 1 - cos(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(sin(x) ** 2)

    Eq << Eq[-1].this.find(sin).apply(Geometry.Sin.eq.Mul.Sinh)

    Eq << Eq[-1].this.find(sinh ** 2).apply(Geometry.Square.Sinh.eq.Sub.Square.Cosh)



if __name__ == '__main__':
    run()
# created on 2020-06-28
# updated on 2023-11-26
