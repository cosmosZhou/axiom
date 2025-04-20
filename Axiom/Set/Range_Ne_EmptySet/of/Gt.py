from util import *


@apply
def apply(given):
    b, a = given.of(Greater)
    assert a.is_integer and b.is_integer
    return Unequal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Set

    a, b = Symbol(integer=True, given=True)
    Eq << apply(b > a)

    Eq << Set.Any_Mem.Range.of.Lt.apply(Eq[0].reversed)

    Eq << Set.Ne_EmptySet.of.Any_Mem.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-18
