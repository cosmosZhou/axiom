from util import *


@apply
def apply(ceil):
    x = ceil.of(Ceiling)

    return Equal(ceil, -floor(-x))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    Eq << apply(ceiling(x))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Element(x, Integers))

    Eq << Eq[-2].this.lhs.apply(sets.el.imply.any_eq)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.eq.imply.eq.ceiling, ret=0)

    Eq << -Eq[-1].this.lhs.expr.args[0]

    Eq << Eq[-1].this.lhs.expr.args[0].apply(algebra.eq.imply.eq.floor)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.given.is_zero)

    Eq << Eq[2].this.lhs.apply(sets.is_noninteger.imply.eq.ceiling, ret=0)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.eq.floor.frac)

    Eq << Eq[-1].this.find(frac).apply(algebra.frac.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.eq.imply.eq.add)




if __name__ == '__main__':
    run()
# created on 2018-05-21
# updated on 2023-05-14
