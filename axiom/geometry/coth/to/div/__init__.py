from util import *


@apply
def apply(self):
    x = self.of(coth)
    return Equal(self, cosh(x) / sinh(x))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(coth(x))

    Eq << Eq[0].this.lhs.apply(geometry.coth.to.inverse.tanh)

    Eq << Eq[-1].this.find(tanh).apply(geometry.tanh.to.div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
from . import add
