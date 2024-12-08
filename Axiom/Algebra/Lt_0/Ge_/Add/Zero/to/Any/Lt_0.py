from util import *


@apply
def apply(lt_zero, add_ge_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = add_ge_zero.of(Expr ** 2 - Expr * Expr * 4 >= 0)
    assert x.is_real and not x.is_given
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c >= 0, x=x)

    Eq.delta_is_nonnegative = Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[1])

    Eq << Eq.delta_is_nonnegative - b

    Eq << Algebra.Lt_0.Ge.to.Le.Div.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] / 2

    Eq << Sets.Le.to.In.Interval.apply(Eq[-1])

    Eq << Sets.In.to.In.relax.apply(Eq[-1], Reals, simplify=None)

    epsilon = Symbol(negative=True)
    Eq << Sets.In.to.In.Add.apply(Eq[-1], epsilon, simplify=None)

    Eq << Algebra.Any.of.Cond.subs.apply(Eq[2], x, Eq[-1].lhs)

    Eq << Algebra.And.of.And.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Expr ** 2).apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.collect)

    Eq << Eq[-1].this.find(Symbol * Add).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Symbol * Add).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1] / epsilon

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[0] * epsilon

    Eq << Algebra.Gt_0.Ge_0.to.Gt_0.Add.apply(Eq[-1], Eq.delta_is_nonnegative)




if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2023-05-15
