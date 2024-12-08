from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Equal(n // 2, (n - 1) / 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    # n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << Algebra.Eq_odd.to.Any.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.to.Eq.Div, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.to.Eq.Floor, ret=0)

    Eq << Eq[-1].this.expr.args[0] - S.One / 2

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.trans)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-12
