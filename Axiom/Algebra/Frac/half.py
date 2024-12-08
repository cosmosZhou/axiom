from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)
    x = -x
    x = x.of(Expr / 2)

    return Equal(fraction, frac(x / 2))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    Eq << apply(frac(-n / 2))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Equal(n % 2, 0))

    Eq <<= Algebra.Imply.of.Imply.And.apply(Eq[-2]), Algebra.Imply.of.Imply.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Equal[0]).apply(Algebra.Eq_even.of.Any), Eq[-1].this.rhs.find(Unequal[0]).apply(Algebra.Ne_.Mod.Zero.of.Any)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Cond.Any.of.Any.And, simplify=None), Eq[-1].this.rhs.apply(Algebra.Cond.Any.of.Any.And, simplify=None)

    Eq <<= Eq[-2].this.find(And).apply(Algebra.Eq.Cond.of.And.subs), Eq[-1].this.find(And).apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_even.to.Any)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_.Mod.Zero.to.Any)





if __name__ == '__main__':
    run()
# created on 2019-05-10
# updated on 2023-08-26
