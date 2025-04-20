from util import *


@apply
def apply(given):
    eq, f = given.of(Imply)
    old, new = eq.of(Equal)
    return Imply(eq, f._subs(old, new))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    y, x = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Equal(t(x), y), Equal(f(t(x), y), g(x))))

    Eq << Logic.Imp.given.Imp.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.given.And.subs, swap=True)




if __name__ == '__main__':
    run()
# created on 2018-07-22
# updated on 2023-08-26
del Bool
from . import Bool
