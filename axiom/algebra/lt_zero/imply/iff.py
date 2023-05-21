from util import *


@apply
def apply(lt_zero, *, cond=None):
    a = lt_zero.of(Expr < 0)
    assert cond.is_Inequality
    lhs, rhs = cond.args
    lhs /= a
    lhs = lhs.ratsimp()
    rhs /= a
    rhs = rhs.ratsimp()
    return Equivalent(cond, cond.reversed_type(lhs, rhs, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, cond= a * x + b < 0)

    Eq << algebra.iff.given.et.infer.apply(Eq[1])

    Eq <<= algebra.infer.given.et.infer.et.apply(Eq[-2], cond=Eq[0]), algebra.infer.given.et.infer.et.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.lt_zero.lt.imply.gt.div)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.gt.imply.lt.mul)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2023-04-11
