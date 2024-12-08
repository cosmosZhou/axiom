from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Imply)
    return Imply(p & cond, q)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, a, b = Symbol(integer=True, given=True)


    f, g = Function(real=True)

    Eq << apply(a > b, Imply(x > y, f(x) > g(y)))

    Eq << Algebra.Imply.of.Or.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0], Eq[-1])

    Eq << Algebra.Imply.to.Or.apply(Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-22
