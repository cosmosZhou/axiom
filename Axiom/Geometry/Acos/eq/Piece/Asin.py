from util import *


@apply
def apply(self):
    x = self.of(acos)
    # assert x in Interval(-1, 1)
    return Equal(self, Piecewise((ArcSin(sqrt(1 - x ** 2)), x >= 0), (S.Pi - ArcSin(sqrt(1 - x ** 2)), True)))


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(acos(x))

    Eq << Eq[0].this.lhs.apply(Geometry.Acos.eq.Add.Asin)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=x >= 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.transport), Eq[-1].this.rhs.apply(Algebra.Eq.transport)

    Eq.is_nonnegative, Eq.is_negative = Eq[-2].this.rhs.reversed, Eq[-1].this.rhs.apply(Algebra.Eq.transport, rhs=0)

    Eq << Eq.is_negative.this.rhs.reversed

    Eq << -Eq[-1].this.rhs

    Eq << Eq.is_nonnegative.this.lhs.apply(Geometry.Ge_0.to.Eq.Add.Asin)

    Eq << Eq[-1].this.lhs.apply(Geometry.Lt_0.to.Eq.Add.Asin)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-14