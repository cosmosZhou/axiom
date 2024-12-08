from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a in Interval(-1, 1)
    assert b in Interval(-1, 1, right_open=True)
    assert domain.left_open and domain.right_open
    return Element(acos(x), Interval(acos(b), acos(a), **domain.kwargs_reversed))


@prove
def prove(Eq):
    from Axiom import Sets, Geometry

    x = Symbol(real=True)
    a = Symbol(domain=Interval(-1, 1))
    b = Symbol(domain=Interval(-1, 1, right_open=True))
    Eq << apply(Element(x, Interval(a, b, right_open=True, left_open=True)))

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq.gt, Eq.lt = Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Element(a, Interval(-1, 1), plausible=True)

    Eq << Element(b, Interval(-1, 1), plausible=True)

    Eq << Sets.In.In.to.Subset.Interval.right_open.apply(Eq[-2], Eq[-1])

    Eq << Subset(Interval(a, b, left_open=True, right_open=True), Interval(a, b, right_open=True), plausible=True)

    Eq << Sets.Subset.Subset.to.Subset.trans.apply(Eq[-1], Eq[-2])

    Eq << Sets.In.Subset.to.In.apply(Eq[0], Eq[-1])

    Eq << Element(b, Interval(-1, 1, right_open=True), plausible=True)

    Eq << Geometry.Lt.In.In.to.Gt.Acos.apply(Eq.lt, Eq[-2], Eq[-1])

    Eq << Geometry.Lt.In.In.to.Gt.Acos.apply(Eq.gt.reversed, Eq[4], Eq[-2]).reversed


if __name__ == '__main__':
    run()
# created on 2020-12-01
