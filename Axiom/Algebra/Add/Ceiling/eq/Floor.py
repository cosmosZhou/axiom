from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr] - 1)
    return Equal(self, (n - sign(d)) // d)


@prove
def prove(Eq):
    from Axiom import Algebra

    n, d = Symbol(integer=True)
    Eq << apply(Ceiling(n / d) - 1)

    Eq << Eq[0].this.find(Ceiling).apply(Algebra.Ceiling.eq.Floor)

    Eq << Eq[-1].this.lhs.find(Floor).apply(Algebra.Floor.eq.Add.quotient)





if __name__ == '__main__':
    run()
# created on 2018-08-11
# updated on 2023-05-29
