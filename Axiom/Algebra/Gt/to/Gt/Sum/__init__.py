from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)
    assert Tuple.is_nonemptyset(limits)
    return Greater(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Greater(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(Algebra.Cond.to.All.restrict, (i, 0, n))

    Eq << Algebra.All_Gt.to.Gt.Sum.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2019-07-24
# updated on 2022-04-01
del Mul
from . import Mul
