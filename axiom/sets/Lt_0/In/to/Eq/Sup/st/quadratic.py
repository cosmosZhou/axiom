from util import *


@apply
def apply(is_negative, el, fx, x=None):
    ab, interval = el.of(Element)
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
    a = is_negative.of(Expr < 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    assert -ab * (2 * a) == b
    return Equal(Sup[x:interval](fx), c - b ** 2 / (4 * a))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, Element(-b / (2 * a), Interval(m, M, left_open=True)), a * x ** 2 + b * x + c, x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sup.eq.Add)

    Eq << Algebra.Lt_0.to.Sup.eq.Mul.Inf.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].this.find(Inf).expr.expand()

    Eq.is_positive = -Eq[0]

    Eq << Algebra.Gt_0.to.Inf.eq.Mul.apply(Eq.is_positive, Eq[-1].find(Inf))

    Eq << -Eq[-1].this.lhs.expr.expand()

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Sets.Gt_0.In.to.Eq.Inf.st.quadratic.apply(Eq.is_positive, Eq[1], Eq[-1].find(Inf).expr, x)
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-26
