from util import *


@apply
def apply(self, index=0, offset=None):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Sup, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= algebra.eq.then.et.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= algebra.sup_le.then.all.le.apply(Eq[-3]), algebra.sup_ge.then.all.any.gt.apply(Eq[-2]), algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.of.all.le.apply(Eq[-2]), algebra.sup_ge.of.all_any_gt.apply(Eq[-1])

    Eq << algebra.all.of.all.limits.subs.offset.apply(Eq[-2], -t)
    Eq << Eq[-1].this.expr.apply(algebra.any.of.any.limits.subs.offset, -t)




if __name__ == '__main__':
    run()
# created on 2019-08-29
