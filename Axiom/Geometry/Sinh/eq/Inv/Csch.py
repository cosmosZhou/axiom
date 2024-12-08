from util import *


@apply
def apply(self):
    x = self.of(sinh)
    return Equal(self, 1 / csch(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(sinh(x))

    Eq << Eq[0].this.find(csch).apply(Geometry.Csch.eq.Inv.Sinh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
