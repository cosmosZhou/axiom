from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(log(r ** z), z * log(r))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    z = Symbol(complex=True, given=True)
    r = Symbol(complex=True)
    Eq << apply(r > 0, z)

    Eq << Algebra.Eq.of.Eq.Exp.apply(Eq[1])

    Eq.el = Sets.Gt_0.to.is_real.Log.apply(Eq[0], simplify=None)

    Eq.x_def = Sets.In.to.Eq.definition.apply(Eq.el)

    Eq << Eq[2].subs(Eq.x_def.reversed)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Eq.to.Eq.Exp.apply(Eq.x_def)

    Eq << Algebra.Eq.to.Eq.Pow.apply(Eq[-1], exp=z)

    Eq << Eq[-4].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-05-20
