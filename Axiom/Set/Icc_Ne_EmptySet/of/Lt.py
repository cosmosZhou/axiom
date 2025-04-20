from util import *


@apply
def apply(given, x=None, left_open=True, right_open=True):
    a, b = given.of(Less)
    if x is None:
        x = given.generate_var(var='x', real=True)

    assert left_open or right_open
    return Unequal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(a < b)

    Eq << Set.Any_Mem.Icc.of.Lt.apply(Eq[0])

    Eq << Set.Ne_EmptySet.of.Any_Mem.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-24
