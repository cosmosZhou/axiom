from util import *


@apply
def apply(given):
    (x, s), (S[x],), *limits = given.of(Any[Element])
    return Any(Element(x, s), (x, s), *limits)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    S = Symbol(etype=dtype.real, given=True)
    e, t = Symbol(real=True)

    Eq << apply(Any[e, t:S](Element(e, S - {t})))

    Eq << Eq[-1].simplify()

    Eq << ~Eq[-1]

    Eq << Sets.Any_In.to.Ne_EmptySet.apply(Eq[0], simplify=None)

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (t, S))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Algebra.Eq.Ne.to.Ne.subs.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()

# created on 2020-07-14
