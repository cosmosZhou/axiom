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
    from Axiom import Geometry, Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Eq[-1].this.lhs.apply(Geometry.Arccos.eq.Add.Arcsin)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=x >= 0)

    Eq <<= Logic.Imp.given.Imp.subs.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subs.Bool.apply(Eq[-1], invert=True)

    Eq.x_is_nonnegative, Eq.x_is_negative = Eq[-2].this.find(acos).apply(Geometry.Arccos.eq.Ite.Arcsin), Eq[-1].this.find(acos).apply(Geometry.Arccos.eq.Ite.Arcsin)

    Eq.sqrt_is_positive = Algebra.Sqrt.gt.Zero.of.Or_Ne_0.apply(Eq[0])

    Eq << Logic.Imp.And.of.Cond.apply(Eq.sqrt_is_positive, cond=Eq.x_is_nonnegative.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.GeDiv.of.Gt_0.Ge)

    Eq <<= Eq.x_is_nonnegative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Algebra.Add.eq.Mul.together)

    Eq << Logic.Imp.And.of.Cond.apply(Eq.sqrt_is_positive, cond=Eq.x_is_negative.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtDiv.of.Gt_0.Lt)

    Eq <<= Eq.x_is_negative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Cond.given.And.subs, invert=True)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Algebra.Add.eq.Mul.together)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2020-12-03
