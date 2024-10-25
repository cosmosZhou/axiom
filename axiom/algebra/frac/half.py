from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)
    x = -x
    x = x.of(Expr / 2)

    return Equal(fraction, frac(x / 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    Eq << apply(frac(-n / 2))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[0], cond=Equal(n % 2, 0))

    Eq <<= algebra.infer.of.infer.et.apply(Eq[-2]), algebra.infer.of.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Equal[0]).apply(algebra.is_even.of.any), Eq[-1].this.rhs.find(Unequal[0]).apply(algebra.mod_ne_zero.of.any)

    Eq <<= Eq[-2].this.rhs.apply(algebra.cond.any.of.any.et, simplify=None), Eq[-1].this.rhs.apply(algebra.cond.any.of.any.et, simplify=None)

    Eq <<= Eq[-2].this.find(And).apply(algebra.eq.cond.of.et.subs), Eq[-1].this.find(And).apply(algebra.eq.cond.of.et.subs)

    Eq << Eq[-2].this.lhs.apply(algebra.is_even.then.any)

    Eq << Eq[-1].this.lhs.apply(algebra.mod_ne_zero.then.any)





if __name__ == '__main__':
    run()
# created on 2019-05-10
# updated on 2023-08-26
