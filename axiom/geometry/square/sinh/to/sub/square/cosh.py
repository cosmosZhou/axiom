from util import *


@apply
def apply(self):
    x = self.of(Sinh ** 2)
    return Equal(self, cosh(x) ** 2 - 1)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(sinh(x) ** 2)

    Eq << Eq[-1].this.find(sinh).apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.lhs.apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(cosh).apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.square.to.add)


if __name__ == '__main__':
    run()
# created on 2023-11-26
