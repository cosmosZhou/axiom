from util import *


@apply
def apply(eq, el):
    t, (R, n) = el.of(Element[CartesianSpace])
    assert R in Interval(0, oo)
    S[t], m = eq.of(Equal[ReducedSum])
    return Element(t, CartesianSpace(Interval(0, m) if R.is_Interval else Range(0, m, right_open=False), n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    t = Symbol(real=True, shape=(oo,))
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Equal(ReducedSum(t[:n]), m), Element(t[:n], CartesianSpace(Interval(0, oo), n)))

    Eq << sets.el_cartesianSpace.imply.all.el.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.ge)

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << algebra.eq_sum.all_ge_zero.imply.all.le.apply(Eq[-1], Eq[-2])

    Eq << sets.el_cartesianSpace.given.all.el.apply(Eq[2])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.given.et)

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
