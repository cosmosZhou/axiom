from util import *


@apply
def apply(imply):
    e, S = imply.of(Element)
    a, b = S.of(Interval)
    assert S.left_open
    return Element(e, Interval(a, b, right_open=S.right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True, right_open=True)))

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Gt.to.Ge.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-27
