from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Subset)

    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), etype=dtype.real)

    Eq << apply(Subset(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (i, 0, n))

    Eq << Sets.All_Subset.to.Subset.Cup.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()

# created on 2021-06-28
