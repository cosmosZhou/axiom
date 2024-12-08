from util import *


@apply
def apply(given, wrt=None):
    cond, q = given.of(Imply)
    if wrt is None:
        wrt = cond.wrt
    return All[wrt:cond](q)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Imply(x > y, f(x) > g(y)))

    Eq << Algebra.Imply.of.Or.apply(Eq[0])

    Eq << Eq[-1].apply(Algebra.Or.of.All, pivot=1)


if __name__ == '__main__':
    run()
# created on 2019-10-04
