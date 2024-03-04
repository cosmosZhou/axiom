from util import *


@apply
def apply(self):
    x = self.of(coth)

    return Equal(self, (Exp(x) + Exp(-x)) / (Exp(x) - Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(coth(x))

    Eq << Eq[0].this.lhs.apply(geometry.coth.to.inverse.tanh)

    Eq << Eq[-1].this.find(Tanh).apply(geometry.tanh.to.div.add.exp)


if __name__ == '__main__':
    run()
# created on 2023-11-26
