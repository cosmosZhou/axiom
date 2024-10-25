from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(Sup(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:m:M](f(x)))

    Eq.reciprocal = algebra.gt_zero.then.gt_zero.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.then.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.then.all.le.apply(Eq[-2]), algebra.sup_ge.then.all.any.gt.apply(Eq[-1], z)

    Eq <<= algebra.all.then.infer.apply(Eq[-2]), algebra.all.then.infer.apply(Eq[-1])

    Eq <<= algebra.cond.infer.then.infer.et.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt_zero.le.then.le.mul), algebra.infer.then.infer.et.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt_zero.gt.then.gt.mul)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.of.et.scale.positive, a)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.of.all.le.apply(Eq[-2]), algebra.sup_ge.of.all_any_gt.apply(Eq[-1], z)

    Eq <<= algebra.all.of.infer.apply(Eq[-2]), algebra.all.of.infer.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-08-21
# updated on 2023-05-14
