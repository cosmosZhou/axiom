from util import *


@apply
def apply(given, var=None):
    arg, m = given.of(Equal[ReducedArgMin])
    k = arg.generate_var(integer=True, var=var)
    n, = arg.shape
    return All[k:n](arg[m] <= arg[k])


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    M = Symbol(integer=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedArgMin(f(x))))

    Eq << Eq[0].this.rhs.apply(algebra.reducedArgMin.to.argmin)


    Eq << algebra.eq_argmin.imply.all.le.apply(Eq[-1], simplify=None)



if __name__ == '__main__':
    run()
# created on 2023-11-05