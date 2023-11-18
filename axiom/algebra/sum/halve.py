from util import *


@apply
def apply(self, *, simplify=True):
    expr, (i, rgn) = self.of(Sum)
    a, b, S[2] = rgn.of(Range)
    rhs = Sum[i:a // 2:(b + (a + 1) % 2) // 2](expr._subs(i, 2 * i + a % 2))
    if simplify:
        rhs = rhs.simplify()
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:Range(a, b, 2)](f[i]))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(a % 2, 0))

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.imply.is_odd)

    Eq <<= algebra.infer.given.infer.subs.apply(Eq[-3]), algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(algebra.is_even.imply.is_odd, ret=0), Eq[-1].this.lhs.apply(algebra.is_odd.imply.is_even, ret=0)

    Eq <<= algebra.infer_et.given.infer.et.subs.apply(Eq[-2], 1), algebra.infer_et.given.infer.et.subs.apply(Eq[-1], 1)

    Eq <<= algebra.infer_et.given.infer.delete.apply(Eq[-2]), algebra.infer_et.given.infer.delete.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.is_even.imply.eq.sum, Eq[0].lhs)

    Eq << Eq[-1].this.lhs.apply(algebra.is_odd.imply.eq.sum, Eq[0].lhs)

    


if __name__ == '__main__':
    run()
# created on 2023-05-30
