from util import *


@apply
def apply(is_zero, contains):
    x = is_zero.of(Equal[Cos, 0])
    S[x], domain = contains.of(Element)
    assert domain in Interval(0, S.Pi)
    assert S.Pi / 2 in domain
    return Equal(x, S.Pi / 2)


@prove
def prove(Eq):
    from Axiom import Set, Geometry

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0), Element(x, Interval(0, S.Pi)))

    Eq.gt = Greater(x, S.Pi / 2, plausible=True)

    Eq << Set.Mem.Icc.Inter.of.Gt.Mem_Icc.apply(Eq.gt, Eq[1])

    Eq << Geometry.Lt_0.Cos.of.Mem_Icc.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    Eq.lt = Less(x, S.Pi / 2, plausible=True)

    Eq << Set.Mem.Icc.Inter.of.Lt.Mem_Icc.apply(Eq.lt, Eq[1])

    Eq << Geometry.Gt_0.Cos.of.Mem_Icc.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]
    Eq <<= ~Eq.gt & ~Eq.lt

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-23
