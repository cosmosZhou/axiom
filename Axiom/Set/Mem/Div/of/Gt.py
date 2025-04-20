from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_finite
    assert b > 0
    return Element(1 / n, Interval.open(0, 1 / b))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    n = Symbol(real=True)
    b = Symbol(real=True, positive=True)
    Eq << apply(n > b)

    Eq << Set.Mem_Icc.given.And.apply(Eq[1])

    Eq << Greater(b, 0, plausible=True)

    Eq << Algebra.Gt.of.Gt.Gt.apply(Eq[0], Eq[-1])

    Eq << Algebra.Gt_0.Div.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GtDiv.of.Gt_0.Gt.apply(Eq[-2], Eq[0])

    Eq << Algebra.GtDiv.of.Gt_0.Gt.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-10-04
