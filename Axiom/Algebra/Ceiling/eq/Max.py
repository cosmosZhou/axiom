from util import *


@apply
def apply(ceil):
    m = ceil.of(Ceiling)
    args = m.of(Max)
    args = [ceiling(arg) for arg in args]

    return Equal(ceil, Max(*args))


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)
    Eq << apply(ceiling(Max(x, y)))

    Eq << Eq[0].apply(Algebra.Eq_Ceiling.of.And)

    Eq <<= Algebra.Gt_Sub_.Ceiling.One.apply(x), Algebra.Gt_Sub_.Ceiling.One.apply(y)

    Eq << Algebra.Gt.Gt.to.Gt.Max.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Add)

    Eq << Eq[-1] + 1


if __name__ == '__main__':
    run()
# created on 2019-03-10
