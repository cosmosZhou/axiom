from util import *


@apply
def apply(self):
    x = self.of(Floor)
    return Equal(self, x - frac(x))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    Eq << apply(floor(x))

    Eq << Eq[-1].this.find(frac).apply(Algebra.Frac.eq.Add)

if __name__ == '__main__':
    run()

# created on 2019-05-11
