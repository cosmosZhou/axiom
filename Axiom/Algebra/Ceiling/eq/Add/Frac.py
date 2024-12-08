from util import *


@apply
def apply(self):
    x = self.of(Ceiling)

    return Equal(self, frac(-x) + x)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    Eq << apply(ceiling(x))

    Eq << Eq[0].this.rhs.args[1].apply(Algebra.Frac.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceiling.eq.Neg.Floor)


if __name__ == '__main__':
    run()
# created on 2019-03-06
