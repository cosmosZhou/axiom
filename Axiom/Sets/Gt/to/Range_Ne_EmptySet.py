from util import *


@apply
def apply(given):
    b, a = given.of(Greater)
    assert a.is_integer and b.is_integer
    return Unequal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(b > a)

    Eq << Sets.Lt.to.Any_In.Range.apply(Eq[0].reversed)

    Eq << Sets.Any_In.to.Ne_EmptySet.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-18
