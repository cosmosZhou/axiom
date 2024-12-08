from util import *


@apply
def apply(eq, el):
    t, (R, n) = el.of(Element[CartesianSpace])
    assert R in Interval(0, oo)
    S[t], m = eq.of(Equal[ReducedSum])
    return Element(t, CartesianSpace(Interval(0, m) if R.is_Interval else Range(0, m, right_open=False), n))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    t = Symbol(real=True, shape=(oo,))
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Equal(ReducedSum(t[:n]), m), Element(t[:n], CartesianSpace(Interval(0, oo), n)))

    Eq << Sets.In_CartesianSpace.to.All.In.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.Ge)

    Eq << Eq[0].this.lhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Algebra.Eq_Sum.All_Ge_0.to.All.Le.apply(Eq[-1], Eq[-2])

    Eq << Sets.In_CartesianSpace.of.All.In.apply(Eq[2])

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.of.And)

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-08-20
