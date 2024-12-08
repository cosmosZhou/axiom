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
    from Axiom import Algebra, Sets

    n = Symbol(integer=True, positive=True)
    t = Symbol(integer=True, shape=(oo,))
    m, k = Symbol(integer=True, nonnegative=True)
    Eq << apply(Equal(ReducedSum(t[:n]), m - k), Element(t[:n], CartesianSpace(Range(0, m + 1), n)))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(Sets.In_CartesianSpace.to.In.CartesianSpace.Range.relax, upper=m + 1)

    Eq << Eq[1].this.lhs.apply(Sets.Eq_Sum.In_CartesianSpace.to.In.CartesianSpace)


if __name__ == '__main__':
    run()
# created on 2023-08-20
