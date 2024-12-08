from util import *


@apply
def apply(eq, interval, x=None):
    fx, f_x = eq.of(Equal)
    assert f_x._subs(x, -x) == fx

    return Equal(Sup[x:-interval](fx), Sup[x:interval](fx))


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(f(x), f(-x)), Interval(m, M, right_open=True), x)

    y = Symbol(Eq[1].rhs)
    Eq << y.this.definition

    Eq <<= Algebra.Eq.to.And.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed)

    z = Symbol(real=True)
    Eq <<= Algebra.LeSup.to.All.Le.apply(Eq[-3]), Algebra.GeSup.to.All.Any.Gt.apply(Eq[-2], z), Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.All.to.All.limits.subs.Neg.real.apply(Eq[-4], x, -x), Eq[-3].this.expr.apply(Algebra.Any.to.Any.limits.Neg), Algebra.LeSup.of.All.Le.apply(Eq[-2]), Algebra.GeSup.of.All_Any_Gt.apply(Eq[-1], z)

    Eq << Eq[-2].subs(Eq[0])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-04-11
