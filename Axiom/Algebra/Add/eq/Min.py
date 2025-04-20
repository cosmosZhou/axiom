from util import *


@apply
def apply(self):
    *z, min_xy = self.of(Expr + Min)
    z = Add(*z)

    args = [e + z for e in min_xy]

    return Equal(self, Min(*args))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True)
    Eq << apply(Min(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(Algebra.Min.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ite.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2018-08-07
