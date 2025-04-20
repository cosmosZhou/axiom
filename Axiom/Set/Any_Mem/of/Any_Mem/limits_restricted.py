from util import *


@apply
def apply(given):
    (x, s), (S[x],), *limits = given.of(Any[Element])
    return Any(Element(x, s), (x, s), *limits)


@prove
def prove(Eq):
    from Axiom import Set, Algebra
    S = Symbol(etype=dtype.real, given=True)
    e, t = Symbol(real=True)

    Eq << apply(Any[e, t:S](Element(e, S - {t})))

    Eq << Eq[-1].simplify()

    Eq << ~Eq[-1]

    Eq << Set.Ne_EmptySet.of.Any_Mem.apply(Eq[0], simplify=None)

    Eq << Algebra.All.of.Cond.restrict.apply(Eq[-1], (t, S))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Algebra.Ne.of.Eq.Ne.subs.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()

# created on 2020-07-14
