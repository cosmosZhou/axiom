from util import *



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(Equal(f(x), g(x)), (x, -oo, oo))

    Eq << Algebra.Eq.of.Eq.invoke.apply(Eq[0], Integral[x:-oo:oo], simplify=False)


if __name__ == '__main__':
    run()

# created on 2020-05-17
