from util import *


@apply
def apply(self):
    x = self.of(cosh)
    return Equal(self, coth(x) * sinh(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(cosh(x))

    Eq << Eq[0].this.find(coth).apply(Geometry.Coth.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
