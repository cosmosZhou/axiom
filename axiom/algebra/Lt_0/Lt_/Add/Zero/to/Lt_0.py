from util import *


@apply
def apply(lt_zero, add_lt_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = add_lt_zero.of(Expr ** 2 - Expr * Expr * 4 < 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return a * x ** 2 + b * x + c < 0


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c < 0, x=x)

    Eq << Sets.Lt_0.to.is_negative.apply(Eq[0], simplify=None)

    Eq.a_reciprocal_is_negative = Sets.is_negative.to.is_negative.Div.apply(Eq[-1])

    t = Symbol(x + Eq.a_reciprocal_is_negative.lhs * b / 2)
    Eq << t.this.definition

    Eq << Algebra.Eq.to.Eq.transport.apply(Eq[-1], rhs=1)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Expr ** 2).apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Lt_0.Lt_0.to.Gt_0.apply(Eq.a_reciprocal_is_negative, Eq[1])

    Eq << -Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add) / 4

    Eq << GreaterEqual(t ** 2, 0, plausible=True)

    Eq << Algebra.Lt_0.Ge_0.to.Le_0.apply(Eq[0], Eq[-1])

    Eq << Algebra.Le_0.Lt_0.to.Lt_0.Add.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()
# created on 2022-04-02
