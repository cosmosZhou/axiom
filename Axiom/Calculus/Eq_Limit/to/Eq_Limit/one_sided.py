from util import *


@apply
def apply(limited_f, dir=1):
    (fx, (x, x0)), A = limited_f.of(Equal[Limit])
    assert dir in (-1, 1)
    return Equal(Limit[x:x0 + dir * S.Infinitesimal](fx), A)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), -1)

    Eq << Calculus.Eq_Limit.of.Any_All.limit_definition.apply(Eq[1])

    delta = Eq[-1].variable
    epsilon = Eq[-1].expr.expr.rhs
    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[0], epsilon, delta)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.GtAbs.equ.Or)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.LtAbs.equ.And)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.of.Cond, 0)

    Eq << Eq[-1].this.find(Greater) + x0

    Eq << Eq[-1].this.find(And[~Less]) + x0

    Eq << Eq[-1].this.find(And).apply(Sets.Cond.Cond.equ.In.Interval)




if __name__ == '__main__':
    run()
# created on 2020-04-26
# updated on 2023-10-15
