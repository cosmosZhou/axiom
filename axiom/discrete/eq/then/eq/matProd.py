from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(MatProduct(lhs, *limits).simplify(), MatProduct(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra, discrete
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.then.all.apply(Eq[0], i)

    Eq << discrete.all_eq.then.eq.matProd.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-10-29
