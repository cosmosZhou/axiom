from util import *


@apply
def apply(ou, reverse=False):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    y = abs(y)
    lhs, rhs = acos(x / r), Piecewise((asin(y / r), x >= 0), (S.Pi - asin(y / r), True))
    if reverse:
        lhs, rhs = rhs, lhs
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Eq[-1].this.lhs.apply(Geometry.Acos.eq.Add.Asin)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=x >= 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq.x_is_nonnegative, Eq.x_is_negative = Eq[-2].this.find(acos).apply(Geometry.Acos.eq.Piece.Asin), Eq[-1].this.find(acos).apply(Geometry.Acos.eq.Piece.Asin)

    Eq.sqrt_is_positive = Algebra.Or_Ne_0.to.Gt_.Sqrt.Zero.apply(Eq[0])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq.sqrt_is_positive, cond=Eq.x_is_nonnegative.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Ge.to.Ge.Div)

    Eq <<= Eq.x_is_nonnegative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Cond.of.And.subs)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Algebra.Add.eq.Mul.together)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq.sqrt_is_positive, cond=Eq.x_is_negative.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Lt.to.Lt.Div)

    Eq <<= Eq.x_is_negative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Cond.of.And.subs, invert=True)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Algebra.Add.eq.Mul.together)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2020-12-03