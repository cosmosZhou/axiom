from util import *


@apply
def apply(self):
    expr = self.of(Unequal[1])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 1))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne_1.to.Eq_even)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne.of.Eq_0)




if __name__ == '__main__':
    run()
# created on 2023-05-22
