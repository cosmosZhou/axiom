from util import *


@apply
def apply(ou):
    x, y = ou.of(Unequal[0] | Unequal[0])
    return Greater(x ** 2 + y ** 2, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Equal(x ** 2 + y ** 2, 0).this.apply(Algebra.Eq_.Add.Zero.to.And.Eq_0)

    Eq.is_nonzero = Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq <<= Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(x), Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(y)

    Eq << Eq[-1] + Eq[-2]
    Eq << Algebra.Ne_0.Ge_0.to.Gt_0.apply(Eq.is_nonzero, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-15