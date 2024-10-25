from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << sets.then.any_el.real.left_open.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.then.et)

    Eq << algebra.cond.any.then.any.et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.gt.le.then.lt.trans, ret=0)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.lt.then.le.strengthen)

    Eq << Eq[-1].this.find(Expr <= -1) + 1

    Eq << Eq[-1].this.expr.args[:2].apply(sets.gt.le.then.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.then.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(algebra.eq.le.then.le.add)





if __name__ == '__main__':
    run()
# created on 2018-10-30
# updated on 2023-05-13
