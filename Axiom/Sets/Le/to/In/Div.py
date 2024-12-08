from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(LessEqual)
    assert n > 0
    return Element(1 / n, Interval(1 / b, oo))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(real=True, positive=True)
    b = Symbol(real=True)
    Eq << apply(n <= b)

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq << Greater(n, 0, plausible=True)

    Eq << Algebra.Gt.Le.to.Gt.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Gt_0.Le.to.Le.Div.apply(Eq[-2], Eq[0])


    Eq << Algebra.Gt_0.Ge.to.Ge.Div.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-04
