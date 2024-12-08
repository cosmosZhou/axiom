from util import *


@apply
def apply(self):
    x = self.of(cos)
    return Equal(self, 1 / sec(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[0].this.find(sec).apply(Geometry.Sec.eq.Inv.Cos)


if __name__ == '__main__':
    run()
# created on 2023-11-26
