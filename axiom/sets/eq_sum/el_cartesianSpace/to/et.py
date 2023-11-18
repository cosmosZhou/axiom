from util import *


@apply
def apply(eq, el):
    t, ((S[0], m), n) = el.of(Element[CartesianSpace[Range]])
    m -= 1
    S[n], = t.shape
    S[t], m_k = eq.of(Equal[ReducedSum])
    assert m_k <= m
    return eq, Element(t, CartesianSpace(Range(0, m_k + 1), n))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    t = Symbol(integer=True, shape=(oo,))
    m, k = Symbol(integer=True, nonnegative=True)
    Eq << apply(Equal(ReducedSum(t[:n]), m - k), Element(t[:n], CartesianSpace(Range(0, m + 1), n)))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << algebra.infer_et.given.infer.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(sets.el_cartesianSpace.imply.el.cartesianSpace.range.relax, upper=m + 1)

    Eq << Eq[1].this.lhs.apply(sets.eq_sum.el_cartesianSpace.imply.el.cartesianSpace)


if __name__ == '__main__':
    run()
# created on 2023-08-20
