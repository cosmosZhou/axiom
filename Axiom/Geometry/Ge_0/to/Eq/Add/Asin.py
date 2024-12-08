from util import *


@apply
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(x) + asin(sqrt(1 - x ** 2)), S.Pi / 2)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra, Sets

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x >= 0)

    Eq << Geometry.Cos.eq.Sub.apply(cos(Eq[1].lhs))

    Eq << Algebra.Ge_0.to.Eq.Abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.any_eq = Geometry.Eq_.Cos.Zero.to.Any.Eq.apply(Eq[-1])

    Eq << LessEqual(x, 1, plausible=True)

    Eq << Sets.Le.Ge.to.In.Interval.apply(Eq[-1], Eq[0])

    Eq <<= Geometry.In.to.In.Asin.apply(Eq[-1]), Sets.In.to.In.Sqrt.Max.apply(Eq[-1])

    Eq << Geometry.In.to.In.Asin.apply(Eq[-1])

    Eq << Sets.In.In.to.In.Add.Interval.apply(Eq[-1], Eq[-3])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.In.Sub, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.In.Div.Interval, S.Pi)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-09
