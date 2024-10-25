from util import *


@apply
def apply(gt_zero, *, cond=None):
    a = gt_zero.of(Expr > 0)
    assert cond.is_Inequality
    lhs, rhs = cond.args
    lhs /= a
    lhs = lhs.ratsimp()
    rhs /= a
    rhs = rhs.ratsimp()
    return Equivalent(cond, cond.func(lhs, rhs, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, cond= a * x + b < 0)

    Eq << algebra.iff.of.et.infer.apply(Eq[1])

    Eq <<= algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-2]), algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.gt_zero.lt.then.lt.div)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.lt.then.lt.mul)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2023-04-11
