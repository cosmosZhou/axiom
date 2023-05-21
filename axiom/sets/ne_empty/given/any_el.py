from util import *




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

    Eq << sets.any_el.imply.ne_empty.apply(Eq[1])










if __name__ == '__main__':
    run()
# created on 2021-06-05
