from util import *


@apply
def apply(self):
    x = self.of(cosh ** 2)
    return Equal(self, sinh(x) ** 2 + 1)


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cosh(x) ** 2)

    Eq << Eq[0].this.find(sinh ** 2).apply(geometry.square.sinh.to.sub.square.cosh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
