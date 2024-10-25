from util import *


@apply
def apply(eq, interval, x=None):
    fx, f_x = eq.of(Equal)
    assert f_x._subs(x, -x) == fx

    return Equal(Sup[x:-interval](fx), Sup[x:interval](fx))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(f(x), f(-x)), Interval(m, M, right_open=True), x)

    y = Symbol(Eq[1].rhs)
    Eq << y.this.definition

    Eq <<= algebra.eq.then.et.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed)

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.then.all.le.apply(Eq[-3]), algebra.sup_ge.then.all.any.gt.apply(Eq[-2], z), algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.all.then.all.limits.subs.negate.real.apply(Eq[-4], x, -x), Eq[-3].this.expr.apply(algebra.any.then.any.limits.negate), algebra.sup_le.of.all.le.apply(Eq[-2]), algebra.sup_ge.of.all_any_gt.apply(Eq[-1], z)

    Eq << Eq[-2].subs(Eq[0])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-04-11
