from util import *



@apply
def apply(given):
    e_set, s = given.of(Unequal[Intersection, EmptySet])
    if not e_set.is_FiniteSet:
        s, e_set = e_set, s

    e = e_set.of(FiniteSet)

    return Element(e, s)


@prove
def prove(Eq):
    from axiom import sets
    s = Symbol(etype=dtype.integer, given=True)
    e = Symbol(integer=True, given=True)

    Eq << apply(Unequal(e.set & s, e.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(sets.notin.imply.is_empty.intersect)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

