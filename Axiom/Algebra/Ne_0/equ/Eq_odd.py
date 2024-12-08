from util import *



@apply
def apply(self):
    expr = self.of(Unequal[0])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 1)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne_0.to.Eq_odd)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.of.Eq_odd)

if __name__ == '__main__':
    run()
# created on 2020-01-27
