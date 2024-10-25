from util import *


@apply
def apply(is_negative, self, div=False):
    a = is_negative.of(Expr < 0)
    fx, *limits = self.of(Inf)
    if div:
        return Equal(self, Sup(fx * a, *limits) / a)
    return Equal(self, a * Sup(fx / a, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < 0, Inf[x:m:M](f(x) * a))

    Eq.reciprocal = algebra.lt_zero.then.lt_zero.div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << algebra.eq.then.et.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.then.all.le.apply(Eq[-2]), algebra.sup_ge.then.all.any.gt.apply(Eq[-1], z)

    Eq <<= algebra.all.then.infer.apply(Eq[-2]), algebra.all.then.infer.apply(Eq[-1])

    Eq <<= algebra.cond.infer.then.infer.et.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.lt_zero.le.then.ge.mul), algebra.infer.then.infer.et.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.lt_zero.gt.then.lt.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.lt.of.et.scale.negative, a)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], z), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq <<= algebra.all.of.infer.apply(Eq[-2]), algebra.all.of.infer.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-12-22
# updated on 2021-10-02