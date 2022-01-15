from util import *


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)

    lhs = Product(lhs, *limits)
    rhs = Product(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.imply.all.apply(Eq[0], i)

    Eq << algebra.all_eq.imply.eq.prod.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-04-09
