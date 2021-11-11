from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Minima(lhs, *limits).simplify(), Minima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), real=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

#     Eq << Eq[-1].subs(Eq[0])
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], Minima[i:n], simplify=False)


if __name__ == '__main__':
    run()

# created on 2019-04-08
# updated on 2019-04-08
