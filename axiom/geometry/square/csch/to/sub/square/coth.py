from util import *


@apply
def apply(self):
    x = self.of(csch ** 2)
    return Equal(self, coth(x) ** 2 - 1)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(csch(x) ** 2)

    Eq << Eq[0].this.find(coth).apply(geometry.coth.to.div)

    Eq << Eq[-1].this.find(cosh ** 2).apply(geometry.square.cosh.to.add.square.sinh)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(sinh).apply(geometry.sinh.to.inverse.csch)

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
