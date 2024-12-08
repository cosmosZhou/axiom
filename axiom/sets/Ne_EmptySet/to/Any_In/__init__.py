from util import *

# given: A != {}
# Any[x] (x in A)


@apply
def apply(given):
    A, B = given.of(Unequal)
    if B:
        assert not A
        A = B
    x = A.element_symbol()
    return Any[x](Element(x, A))


@prove
def prove(Eq):
    from Axiom import Sets

    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq << Sets.NotIn.to.Eq_EmptySet.EmptySet_definition.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()


# created on 2018-03-06

from . import st
