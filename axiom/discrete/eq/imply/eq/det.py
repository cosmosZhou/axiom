from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(det(lhs), det(rhs))


@prove
def prove(Eq):
    from axiom import algebra
    n, m = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(m, m), integer=True)

    Eq << apply(Equal(f(i), g(i)))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], det)


if __name__ == '__main__':
    run()

# created on 2020-02-10
