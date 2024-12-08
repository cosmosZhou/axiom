from util import *



@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Imply)
    return Imply(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q, r = Symbol(bool=True)
    Eq << apply(Imply(p, q), cond=r)

    Eq << Algebra.Imply.to.Or.apply(Eq[0])

    Eq << Algebra.Imply.of.Or.apply(Eq[1])

    Eq << Algebra.Or.of.And.apply(Eq[-1])

    Eq << Algebra.Or.of.Or.apply(Eq[-1], slice(0, 3, 2))





if __name__ == '__main__':
    run()
# created on 2019-10-05
# updated on 2022-01-27
