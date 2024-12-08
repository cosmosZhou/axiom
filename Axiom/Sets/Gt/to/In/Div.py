from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_finite
    assert b > 0
    return Element(1 / n, Interval.open(0, 1 / b))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(real=True)
    b = Symbol(real=True, positive=True)
    Eq << apply(n > b)

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq << Greater(b, 0, plausible=True)

    Eq << Algebra.Gt.Gt.to.Gt.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[-1])

    Eq << Algebra.Gt_0.Gt.to.Gt.Div.apply(Eq[-2], Eq[0])

    Eq << Algebra.Gt_0.Gt.to.Gt.Div.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-10-04
