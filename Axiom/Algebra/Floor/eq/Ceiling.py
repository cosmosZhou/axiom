from util import *


@apply
def apply(self, *, evaluate=False):
    plus, d = self.of(Floor[Expr / Expr])
    n = plus - d + sign(d)
    return Equal(self, Ceiling(n / d, evaluate=evaluate))


@prove
def prove(Eq):
    from Axiom import Algebra

    n, d = Symbol(integer=True)
    Eq << apply(n // d)

    Eq << Algebra.Ceiling.eq.Floor.apply(Eq[0].rhs).reversed





if __name__ == '__main__':
    run()
# created on 2019-05-09
# updated on 2023-05-29
