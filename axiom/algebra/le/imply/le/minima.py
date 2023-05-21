from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)
    assert Tuple.is_nonemptyset(limits)
    return LessEqual(Minima(lhs, *limits).simplify(), Minima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(LessEqual(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))
    
    Eq << algebra.all_le.imply.le.minima.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-23
