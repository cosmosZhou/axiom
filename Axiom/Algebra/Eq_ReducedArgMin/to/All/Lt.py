from util import *


@apply
def apply(given, var=None):
    arg, m = given.of(Equal[ReducedArgMin])
    k = arg.generate_var(integer=True, var=var)
    n, = arg.shape
    return All[k:m](arg[m] < arg[k])


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    M = Symbol(integer=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedArgMin(f(x))))

    Eq << Eq[0].this.rhs.apply(Algebra.ReducedArgMin.eq.ReducedArgMax.Neg)

    Eq << Algebra.Eq_ReducedArgMax.to.All.Gt.apply(Eq[-1])

    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2023-11-05