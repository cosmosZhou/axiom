from util import *


@apply
def apply(gt_zero, x=None):
    b, (a, c) = gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(b ** 2 - 4 * a * c > 0, x=x)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=Unequal(a, 0))

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=Equal(a, 0))

    Eq << Logic.ImpEq.of.ImpEq.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne.of.Gt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sqrt.ne.Zero.of.Ne_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.of.Abs.ne.Zero)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.Lt_0.of.Ne_0, x=x, b=c)

    Eq << Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[2].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.Lt_0.of.Ne_0.Add.gt.Zero, x=x)





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2025-04-20
