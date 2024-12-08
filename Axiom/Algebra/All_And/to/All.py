from util import *


@apply
def apply(given, index=0):
    eqs, *limits = given.of(All[And])
    eq = eqs[index]
    return All(eq, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    a, b, c, d = Symbol(real=True, given=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[x:a:b]((x <= c) & (f(x) >= d)), index=0)

    Eq << ~Eq[-1]

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()


# created on 2018-10-01
