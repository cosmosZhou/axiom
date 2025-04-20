from util import *



@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)
    assert limits
    lhs, rhs = Sum(lhs, *limits), Sum(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Algebra.All.of.Cond.apply(Eq[0], i)

    Eq << Algebra.EqSum.of.All_Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-19

del Eq
from . import Eq
