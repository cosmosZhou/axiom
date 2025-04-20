from util import *



@apply
def apply(given, index):
    x, S = given.of(Element)
    a = given.generate_var(**x.type.dict)
    return Any[a:S](Equal(x[index], a[index]))


@prove
def prove(Eq):
    from Axiom import Set, Algebra
    n = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    S = Symbol(etype=dtype.integer[n])

    Eq << apply(Element(x, S), index=i)

    a = Eq[-1].variable

    Eq << Algebra.Any.given.Any.subs.apply(Eq[-1], a, x)

    Eq << Set.Any_Mem.given.Ne_EmptySet.apply(Eq[-1])

    Eq << Set.Ne_EmptySet.of.Mem.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-03-02
