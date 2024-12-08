from util import *


@apply
def apply(gt_zero, x=None):
    b, (a, c) = gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(b ** 2 - 4 * a * c > 0, x=x)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=Unequal(a, 0))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Equal(a, 0))

    Eq << Algebra.Imply.to.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.to.Ne_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.to.Ne_0.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_.Abs.Zero.to.Ne_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.to.Any.Lt_0, x=x, b=c)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[2].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Gt_.Add.Zero.to.Any.Lt_0, x=x)





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2022-04-03
