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
    from axiom import sets

    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq << sets.notin.imply.is_empty.empty_definition.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()


from . import st
# created on 2018-03-06
