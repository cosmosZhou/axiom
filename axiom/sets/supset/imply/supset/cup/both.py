from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Supset)

    return Supset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), etype=dtype.real)

    Eq << apply(Supset(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq << sets.all_supset.imply.supset.union.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()

# created on 2021-07-03
# updated on 2021-07-03
