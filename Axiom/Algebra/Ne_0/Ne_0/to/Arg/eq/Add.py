from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    s = Arg(x) + Arg(y)
    return Equal(Arg(x * y), s - Ceiling(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[0])

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[1])

    Eq.abs_is_positive = Eq[-1] * Eq[-2]

    Eq <<= Algebra.Expr.eq.Mul.ExpI.apply(x), Algebra.Expr.eq.Mul.ExpI.apply(y)

    Eq << Eq[-1] * Eq[-2]

    Eq << Algebra.Eq.to.Eq.Arg.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Eq.Arg.apply(Eq.abs_is_positive, Mul(*Eq[-1].rhs.arg.args[2:]))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq << Eq[-1].this.rhs.apply(Algebra.Arg.ExpI.eq.Add.Ceiling)


if __name__ == '__main__':
    run()
# created on 2018-10-25
