from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Equal[EmptySet])

    A, B = AB.of(Intersection)
    if wrt is None:
        wrt = given.generate_var(**A.etype.dict)

    return All[wrt:A](NotElement(wrt, B))


@prove
def prove(Eq):
    from Axiom import Set
    B, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(A & B, A.emptySet))

    Eq << ~Eq[1]

    Eq << Set.Any_And_Mem.of.Any.apply(Eq[-1])

    Eq << Set.Ne_EmptySet.of.Any_Mem.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-05-12
