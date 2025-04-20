from util import *


@apply
def apply(given, index=None):
    et, f = given.of(Imply)
    eqs = et.of(And)
    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                break

    eq = eqs[index]
    old, new = eq.of(Equal)

    return Imply(et, f._subs(old, new))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Equal(t(x), y) & (f(x) > y), Equal(f(t(x), y), g(x))))

    Eq << Logic.Imp.given.Imp.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.args[:2].apply(Algebra.Eq.Cond.given.And.subs, swap=True)





if __name__ == '__main__':
    run()
# created on 2018-06-11
# updated on 2023-08-26

del Bool
from . import Bool
