from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Greater(frac(x), 0)


@prove
def prove(Eq):
    from Axiom import Set
    x = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Set.Fract.ne.Zero.of.NotMem.apply(Eq[0])

    Eq << Element(frac(x), Interval(0, 1, right_open=True), plausible=True)

    Eq << Set.Mem_SDiff.of.Mem.Ne.apply(Eq[-2], Eq[-1])

    Eq << Set.And.of.Mem_Icc.apply(Eq[-1])

if __name__ == '__main__':
    run()
# created on 2018-05-11
