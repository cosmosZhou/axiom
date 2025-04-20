from util import *



# given e not in S
@apply
def apply(given):
    e, s = given.of(NotElement)
    return Equal(e.set & s, e.emptySet)


@prove
def prove(Eq):
    from Axiom import Set

    s = Symbol(etype=dtype.integer, given=True)
    e = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, s))

    Eq << ~Eq[-1]

    Eq << Set.Any_Mem.of.Inter_Ne_EmptySet.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2019-01-31
