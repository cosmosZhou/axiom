from util import *


@apply
def apply(self):
    x = self.of(-Ceiling)
    return Equal(self, floor(-x))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    Eq << apply(-ceiling(x))

    Eq << Eq[0].this.rhs.apply(Algebra.Floor.eq.Neg.Ceiling)


if __name__ == '__main__':
    run()
# created on 2020-01-29
