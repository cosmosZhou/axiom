from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(GreaterEqual)
    assert Tuple.is_nonemptyset(limits)
    return GreaterEqual(Sup(lhs, *limits).simplify(), Sup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.then.all.restrict, (i, 0, n))

    Eq << algebra.all_ge.then.ge.sup.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-23
