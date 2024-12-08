from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal[Expr ** 2, Expr])
    _b = b.of(Expr ** 2)
    if _b is None:
        _b = sqrt(b)

    return Equal(a - _b, 0) | Equal(a + _b, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(complex=True, given=True)
    Eq << apply(Equal(a ** 2, b ** 2))

    Eq << Algebra.Or_Eq_0.of.Eq_.Mul.Zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add, deep=True).reversed


if __name__ == '__main__':
    run()
# created on 2018-11-13
