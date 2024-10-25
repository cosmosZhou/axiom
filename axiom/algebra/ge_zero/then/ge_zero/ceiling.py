from util import *


@apply(simplify=None)
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    return GreaterEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << sets.then.any_el.real.left_open.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.then.et)

    Eq << algebra.cond.any.then.any.et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.le.ge.then.ge.trans, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(sets.gt.le.then.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.then.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(algebra.eq.ge.then.ge.add)




if __name__ == '__main__':
    run()
# created on 2019-03-11
# updated on 2023-05-14
