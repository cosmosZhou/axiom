from util import *


@apply
def apply(ne_zero, x=None, b=None):
    a = ne_zero.of(Unequal[0])
    assert x.is_real
    assert a.is_real and b.is_real
    return Any[x](a * x + b < 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(Unequal(a, 0), x=x, b=b)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=a > 0)

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.to.Any.Lt_0, x=x, b=b)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt_0.to.Any.Lt_0.simple, x=x, b=b)




if __name__ == '__main__':
    run()
# created on 2022-04-03
