from util import *


@apply
def apply(is_positive, el, fx, x=None):
    ab, interval = el.of(Element)
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
    a = is_positive.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    assert -ab * (2 * a) == b
    return Equal(Inf[x:interval](fx), c - b ** 2 / (4 * a))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, Element(-b / (2 * a), Interval(m, M, right_open=True)), a * x ** 2 + b * x + c, x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Inf.limits.subs.offset, Eq[1].lhs)

    Eq << Eq[-1].this.lhs.expr.expand()

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Inf.eq.Mul.apply(Eq[-1], Eq[-2].lhs) * a

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Algebra.Eq.of.Eq.Div.apply(Eq[-1], a)

    Eq << Sets.In.to.In.Sub.apply(Eq[1], Eq[1].lhs)

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq << Algebra.Gt_0.Le_0.to.Inf_Square.eq.Zero.apply(Eq[-1], Eq[-2], left_open=False, x=x)


if __name__ == '__main__':
    run()
# created on 2019-12-25
