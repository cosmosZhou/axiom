from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[0])

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[1])

    Eq << Algebra.Gt_0.Gt_0.to.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Abs)

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[-1])

    Eq << Algebra.Ne_.Abs.Zero.to.Ne_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-03-19
# updated on 2022-04-03
