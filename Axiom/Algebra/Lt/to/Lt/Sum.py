from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)
    assert Tuple.is_nonemptyset(limits)
    return Less(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Less(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (i, 0, n))

    Eq << Algebra.All_Lt.to.Lt.Sum.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2020-01-03
# updated on 2022-04-01