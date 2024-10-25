from util import *


@apply
def apply(limited_f, dir=1):
    (fx, (x, x0)), A = limited_f.of(Equal[Limit])
    assert dir in (-1, 1)
    return Equal(Limit[x:x0 + dir * S.Infinitesimal](fx), A)


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), -1)

    Eq << calculus.eq_limit.of.any_all.limit_definition.apply(Eq[1])

    delta = Eq[-1].variable
    epsilon = Eq[-1].expr.expr.rhs
    Eq << calculus.eq_limit.then.any.all.limit_definition.apply(Eq[0], epsilon, delta)

    Eq << Eq[-1].this.find(Greater).apply(algebra.abs_gt.to.ou)

    Eq << Eq[-1].this.find(And[~Less]).apply(algebra.abs_lt.to.et)

    Eq << Eq[-1].this.find(And).apply(algebra.et.to.ou)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.of.cond, 0)

    Eq << Eq[-1].this.find(Greater) + x0

    Eq << Eq[-1].this.find(And[~Less]) + x0

    Eq << Eq[-1].this.find(And).apply(sets.cond.cond.to.el.interval)




if __name__ == '__main__':
    run()
# created on 2020-04-26
# updated on 2023-10-15
