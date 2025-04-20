from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    assert interval in Interval(0, 1, left_open=True)
    return log(x) <= 0


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(f(x), Interval(0, 1, left_open=True)))

    Eq << Set.Eq.of.Mem.definition.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Set.Gt.of.Mem_Icc.apply(Eq[0])

    Eq << Algebra.Ne.of.Gt.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-04-17
# updated on 2025-04-20
