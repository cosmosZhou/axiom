from util import *


@apply
def apply(imply):
    eqs, *limits = imply.of(Any[Or])

    return Or(*(Any(eq, *limits) for eq in eqs))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real, given=True)

    f, g = Function(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(Algebra.All.All.to.All.And)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-09-30
