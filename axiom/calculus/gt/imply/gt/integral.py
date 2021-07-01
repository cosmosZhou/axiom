from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)

    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import calculus, algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(Greater(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (x, a, b))

    Eq << calculus.all_gt.imply.gt.integral.apply(Eq[-1])


if __name__ == '__main__':
    run()
