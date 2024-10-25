from util import *


@apply
def apply(self, index=0, offset=None):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Inf, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= algebra.eq.then.et.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= algebra.inf_le.then.all.any.lt.apply(Eq[-3]), algebra.inf_ge.then.all.ge.apply(Eq[-2]), algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2]), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(algebra.any.of.any.limits.subs.offset, -t)
    Eq << algebra.all.of.all.limits.subs.offset.apply(Eq[-1], -t)



if __name__ == '__main__':
    run()
# created on 2019-10-03
