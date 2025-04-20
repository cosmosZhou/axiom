from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(log(r ** z), z * log(r))


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    z = Symbol(complex=True, given=True)
    r = Symbol(complex=True)
    Eq << apply(r > 0, z)

    Eq << Algebra.Eq.given.Eq.Exp.apply(Eq[1])

    Eq.el = Set.IsReal.Log.of.Gt_0.apply(Eq[0], simplify=None)

    Eq.x_def = Set.Eq.of.Mem.definition.apply(Eq.el)

    Eq << Eq[2].subs(Eq.x_def.reversed)

    Eq << Algebra.And.given.And.apply(Eq[-1])

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Algebra.EqExp.of.Eq.apply(Eq.x_def)

    Eq << Algebra.EqPowS.of.Eq.apply(Eq[-1], exp=z)

    Eq << Eq[-4].subs(Eq[-1].reversed)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2025-04-20
del Eq
from . import Eq
