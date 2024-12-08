from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    assert not x.is_set
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << Eq[0].this.lhs.arg.apply(Algebra.Expr.eq.Add.complex)

    Eq.Square_is_zero = Algebra.Eq.to.Eq.Pow.apply(Eq[-1], exp=2)

    Eq.Im_is_positive = Greater(Im(x) ** 2, 0, plausible=True)

    Eq << GreaterEqual(Re(x) ** 2, 0, plausible=True)

    Eq << Algebra.Gt_0.Ge_0.to.Gt_0.Add.apply(Eq.Im_is_positive, Eq[-1])

    Eq << Eq[-1].subs(Eq.Square_is_zero)

    Eq << ~Eq.Im_is_positive

    Eq << Algebra.Le_0.to.Eq_0.apply(Eq[-1])

    Eq.Im_is_zero = Algebra.Eq_.Square.Zero.to.Eq_0.real.apply(Eq[-1])

    Eq.Re_is_positive = Greater(Re(x) ** 2, 0, plausible=True)

    Eq << GreaterEqual(Im(x) ** 2, 0, plausible=True)

    Eq << Algebra.Gt_0.Ge_0.to.Gt_0.Add.apply(Eq.Re_is_positive, Eq[-1])

    Eq << Eq[-1].subs(Eq.Square_is_zero)

    Eq << ~Eq.Re_is_positive

    Eq << Algebra.Le_0.to.Eq_0.apply(Eq[-1])

    Eq.Re_is_zero = Algebra.Eq_.Square.Zero.to.Eq_0.real.apply(Eq[-1])

    Eq << Algebra.Expr.eq.Add.complex.apply(x)

    Eq << Eq[-1].subs(Eq.Im_is_zero, Eq.Re_is_zero)


if __name__ == '__main__':
    run()

# created on 2018-03-16

from . import real
