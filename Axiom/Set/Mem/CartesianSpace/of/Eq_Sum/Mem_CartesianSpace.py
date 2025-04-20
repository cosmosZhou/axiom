from util import *


@apply
def apply(eq, el):
    t, (R, n) = el.of(Element[CartesianSpace])
    assert R in Interval(0, oo)
    S[t], m = eq.of(Equal[ReducedSum])
    return Element(t, CartesianSpace(Interval(0, m) if R.is_Interval else Range(0, m, right_open=False), n))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    n = Symbol(integer=True, positive=True)
    t = Symbol(real=True, shape=(oo,))
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Equal(ReducedSum(t[:n]), m), Element(t[:n], CartesianSpace(Interval(0, oo), n)))

    Eq << Set.All.Mem.of.Mem_CartesianSpace.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(Set.Ge.of.Mem_Icc)

    Eq << Eq[0].this.lhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Algebra.All.Le.of.Eq_Sum.All_Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Set.Mem_CartesianSpace.given.All.Mem.apply(Eq[2])

    Eq << Eq[-1].this.expr.apply(Set.Mem_Icc.given.And)

    Eq << Algebra.All_And.given.And.All.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-08-20
