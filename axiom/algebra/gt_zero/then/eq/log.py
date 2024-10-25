from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(log(r ** z), z * log(r))


@prove
def prove(Eq):
    from axiom import algebra, sets

    z = Symbol(complex=True, given=True)
    r = Symbol(complex=True)
    Eq << apply(r > 0, z)

    Eq << algebra.eq.of.eq.exp.apply(Eq[1])

    Eq.el = sets.gt_zero.then.is_real.log.apply(Eq[0], simplify=None)

    Eq.x_def = sets.el.then.eq.definition.apply(Eq.el)

    Eq << Eq[2].subs(Eq.x_def.reversed)

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[0])

    Eq << algebra.eq.then.eq.exp.apply(Eq.x_def)

    Eq << algebra.eq.then.eq.pow.apply(Eq[-1], exp=z)

    Eq << Eq[-4].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-05-20
