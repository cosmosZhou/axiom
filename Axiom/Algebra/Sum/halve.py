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
    from Axiom import Algebra

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:Range(a, b, 2)](f[i]))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Equal(a % 2, 0))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.to.Eq_odd)

    Eq <<= Algebra.Imply.of.Imply.subs.apply(Eq[-3]), Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Eq_even.to.Eq_odd, ret=0), Eq[-1].this.lhs.apply(Algebra.Eq_odd.to.Eq_even, ret=0)

    Eq <<= Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-2], 1), Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1], 1)

    Eq <<= Algebra.Imply_And.of.Imply.delete.apply(Eq[-2]), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_even.to.Eq.Sum, Eq[0].lhs)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_odd.to.Eq.Sum, Eq[0].lhs)




if __name__ == '__main__':
    run()
# created on 2023-05-30
