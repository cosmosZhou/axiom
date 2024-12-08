from util import *


@apply
def apply(self):
    x = self.of(Tanh)

    return Equal(self, (Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x = Symbol(real=True)
    Eq << apply(tanh(x))

    Eq << Eq[0].this.lhs.apply(Geometry.Tanh.eq.Div)

    Eq << Eq[-1].this.find(sinh).apply(Geometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.find(cosh).apply(Geometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.lhs.apply(Algebra.Div.cancel, 2)




if __name__ == '__main__':
    run()
# created on 2023-11-26
