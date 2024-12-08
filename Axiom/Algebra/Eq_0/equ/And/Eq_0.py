from util import *


@apply
def apply(self):
    z = self.of(Equal[0])
    x = Re(z)
    y = Im(z)
    return Equal(x, 0) & Equal(y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Equal(z, 0))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.lhs.apply(Algebra.Expr.eq.Add.complex)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.to.Eq.Abs)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.to.Eq.Pow, exp=2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_.Add.Zero.to.And.Eq_0)

    Eq << Eq[2].this.rhs.lhs.apply(Algebra.Expr.eq.Add.complex)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()
# created on 2018-06-11
# updated on 2023-05-20
