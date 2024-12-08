from util import *


@apply
def apply(pow):
    z, n = pow.of(Arg[Pow])
    assert n.is_integer and n > 0
    return Equal(pow, Arg(z) * n - Ceiling(Arg(z) * n / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from Axiom import Algebra

    z = Symbol(complex=True, given=True)
    n = Symbol(integer=True, given=True, positive=True)
    Eq << apply(Arg(z ** n))

    Eq << Eq[-1].this.lhs.arg.base.apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Eq[-1].this.lhs.arg.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Unequal(z, 0))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne_0.to.Gt_0.Abs)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Gt_0.Pow, n)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Eq.Arg, Eq[-1].find(Exp))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceiling)


if __name__ == '__main__':
    run()
# created on 2018-08-26
