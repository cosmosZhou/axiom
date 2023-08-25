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

    Eq.reciprocal = algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.imply.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.imply.all_le.apply(Eq[-2]), algebra.sup_ge.imply.all.any.gt.apply(Eq[-1], z)

    Eq <<= algebra.all.imply.infer.apply(Eq[-2]), algebra.all.imply.infer.apply(Eq[-1])

    Eq <<= algebra.cond.infer.imply.infer.et.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt_zero.le.imply.le.mul), algebra.infer.imply.infer.et.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.imply.any.et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.gt_zero.gt.imply.gt.mul)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.given.et.scale.positive, a)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.given.all_le.apply(Eq[-2]), algebra.sup_ge.given.all_any_gt.apply(Eq[-1], z)

    Eq <<= algebra.all.given.infer.apply(Eq[-2]), algebra.all.given.infer.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-08-21
# updated on 2023-05-14
