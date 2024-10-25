from util import *


@apply
def apply(self):
    x = self.of(Tanh)

    return Equal(self, (Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(tanh(x))

    Eq << Eq[0].this.lhs.apply(geometry.tanh.to.div)

    Eq << Eq[-1].this.find(sinh).apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.find(cosh).apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.lhs.apply(algebra.div.cancel, 2)




if __name__ == '__main__':
    run()
# created on 2023-11-26
