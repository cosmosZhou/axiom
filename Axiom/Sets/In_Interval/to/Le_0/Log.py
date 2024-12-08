from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    assert interval in Interval(0, 1, left_open=True)
    return log(x) <= 0


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(f(x), Interval(0, 1, left_open=True)))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Sets.In_Interval.to.Gt.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-17
