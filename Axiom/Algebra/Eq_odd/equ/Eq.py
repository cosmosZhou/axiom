from util import *



@apply
def apply(self):
    n = self.of(Equal[Expr % 2, 1])
    return Equal((-1) ** n, -1)


@prove
def prove(Eq):
    from Axiom import Algebra
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 1))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_odd.to.Eq.Pow)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_odd.of.Eq)


if __name__ == '__main__':
    run()
# created on 2019-10-13