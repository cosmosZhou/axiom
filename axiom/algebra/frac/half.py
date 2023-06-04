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

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(n % 2, 0))

    Eq <<= algebra.infer.given.infer.et.apply(Eq[-2]), algebra.infer.given.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Equal[0]).apply(algebra.is_even.given.any), Eq[-1].this.rhs.find(Unequal[0]).apply(algebra.mod_ne_zero.given.any)

    Eq <<= Eq[-2].this.rhs.apply(algebra.cond.any.given.any_et, simplify=None), Eq[-1].this.rhs.apply(algebra.cond.any.given.any_et, simplify=None)

    Eq <<= Eq[-2].this.find(And).apply(algebra.et.given.et.subs.eq), Eq[-1].this.find(And).apply(algebra.et.given.et.subs.eq)

    Eq << Eq[-2].this.lhs.apply(algebra.is_even.imply.any)

    Eq << Eq[-1].this.lhs.apply(algebra.mod_ne_zero.imply.any)

    
    


if __name__ == '__main__':
    run()
# created on 2019-05-10
# updated on 2023-05-26
