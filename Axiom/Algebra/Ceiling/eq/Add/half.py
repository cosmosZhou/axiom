from util import *


@apply
def apply(self):
    x, n = self.of(Ceiling[Expr + Expr / 2])
    assert n.is_odd

    return Equal(self, Ceiling(x - S.One / 2) + (n + 1) / 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, odd=True, positive=True)
    Eq << apply(Ceiling(x + n / 2))

    Eq << Eq[0].this.rhs.apply(Algebra.Add.eq.Ceiling)


if __name__ == '__main__':
    run()
# created on 2018-11-08
