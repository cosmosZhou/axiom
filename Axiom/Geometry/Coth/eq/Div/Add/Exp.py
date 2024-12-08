from util import *


@apply
def apply(self):
    x = self.of(coth)
    return Equal(self, (Exp(x) + Exp(-x)) / (Exp(x) - Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(coth(x))

    Eq << Eq[0].this.lhs.apply(Geometry.Coth.eq.Inv.Tanh)

    Eq << Eq[-1].this.find(Tanh).apply(Geometry.Tanh.eq.Div.Add.Exp)


if __name__ == '__main__':
    run()
# created on 2023-11-26
