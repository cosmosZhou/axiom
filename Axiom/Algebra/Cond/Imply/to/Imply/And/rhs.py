from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Imply)
    return Imply(p, q & cond)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(a > b, Imply(x > y, f(x) > g(y)))

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Or.apply(Eq[-1])

    Eq << Algebra.Cond.to.Or.apply(Eq[0], cond=x <= y)


if __name__ == '__main__':
    run()
# created on 2018-09-12
