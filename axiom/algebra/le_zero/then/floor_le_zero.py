from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << sets.then.any_el.real.apply(x)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.then.et)

    Eq << algebra.cond.any.then.any.et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.le.ge.then.ge.trans, ret=1)

    Eq << Eq[-1].this.expr.args[::2].apply(sets.lt.ge.then.el.interval)

    Eq << Eq[-1].this.expr.args[1].apply(sets.el.then.eq.floor)

    Eq << Eq[-1].this.expr.apply(algebra.ge.eq.then.ge.trans)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-12-06
# updated on 2023-05-18
