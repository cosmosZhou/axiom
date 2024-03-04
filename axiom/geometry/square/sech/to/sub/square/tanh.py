from util import *


@apply
def apply(self):
    x = self.of(sech ** 2)
    return Equal(self, 1 - tanh(x) ** 2)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(sech(x) ** 2)

    Eq << Eq[0].this.find(tanh).apply(geometry.tanh.to.div)

    Eq << Eq[-1].this.find(sinh ** 2).apply(geometry.square.sinh.to.sub.square.cosh)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(cosh).apply(geometry.cosh.to.inverse.sech)


if __name__ == '__main__':
    run()
# created on 2023-11-26
