from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Inf)
    return Equal(Inf(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Inf[x:m:M](f(x)))

    Eq.reciprocal = algebra.gt_zero.then.gt_zero.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.then.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.inf_le.then.all.any.lt.apply(Eq[-2], z), algebra.inf_ge.then.all.ge.apply(Eq[-1])

    Eq <<= algebra.all.then.infer.apply(Eq[-2]), algebra.all.then.infer.apply(Eq[-1])

    Eq <<= Eq[-2].subs(z, z * Eq.reciprocal.lhs), algebra.cond.infer.then.infer.et.rhs.apply(Eq[0], Eq[-1])

    Eq <<= algebra.infer.then.infer.et.both_sided.apply(Eq[-2], cond=Eq[0]), Eq[-1].this.rhs.apply(algebra.gt_zero.ge.then.ge.mul)

    Eq << Eq[-2].this.rhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt_zero.lt.then.lt.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.gt.of.et.scale.positive, a)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], z), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq <<= algebra.all.of.infer.apply(Eq[-2]), algebra.all.of.infer.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-13
