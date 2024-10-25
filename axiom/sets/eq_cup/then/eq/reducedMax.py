from util import *


@apply
def apply(eq):
    (ai, limit), (bi, S[limit]) = eq.of(Equal[Cup[FiniteSet], Cup[FiniteSet]])
    i, S[0], n = limit
    a = Lamda[i:n](ai).simplify()
    b = Lamda[i:n](bi).simplify()
    return Equal(ReducedMax(a), ReducedMax(b))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    a, b, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(a[:n].cup_finiteset(), b[:n].cup_finiteset()))

    Eq <<= sets.then.el_cup.reducedMax.apply(Eq[1].lhs.arg), sets.then.el_cup.reducedMax.apply(Eq[1].rhs.arg)

    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0].reversed)

    Eq <<= sets.el_cup.then.le_reducedMax.apply(Eq[-2]), sets.el_cup.then.le_reducedMax.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-11-12
