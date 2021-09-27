from util import *


@apply
def apply(is_empty, eq_complement):
    A, B = is_empty.of(Equal[Intersection, EmptySet])    
    (_A, _B), C = eq_complement.of(Equal[Complement])
    assert {A, B} == {_A, _B}
    return Equal(_A, C)


@prove
def prove(Eq):
    from axiom import sets

    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet), Equal(A - B, C))

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()