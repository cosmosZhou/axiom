from util import *


@apply
def apply(self):
    return Equal(ReducedMax(self), self[ReducedArgMax(self)])


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    k = Symbol(Eq[0].find(ReducedArgMax))
    Eq << k.this.defun()

    Eq << Eq[0].subs(Eq[1].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMax.to.maxima)

    Eq << algebra.imply.all.le_maxima.apply(Eq[-1].lhs)

    i = Eq[-1].variable
    Eq.le = algebra.all.imply.cond.subs.apply(Eq[-1], i, k)

    Eq << algebra.eq_reducedArgMax.imply.all.ge.apply(Eq[1])

    Eq << Eq[-1].this.expr.reversed

    Eq << algebra.all_le.imply.maxima_le.apply(Eq[-1])

    
    Eq <<= Eq[-1] & Eq.le


if __name__ == '__main__':
    run()
# created on 2023-11-12
# updated on 2023-11-13
