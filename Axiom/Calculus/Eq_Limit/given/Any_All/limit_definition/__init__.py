from util import *


@apply
def apply(given, epsilon=None, delta=None):
    from Axiom.Calculus.Eq.Is.Any_All.limit_definition import Any_All
    return Any_All(given, epsilon, delta)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Logic

    a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq << Calculus.Eq.Is.Any_All.limit_definition.apply(Eq[0])

    Eq << Logic.Cond.of.Cond.Iff.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-04-26

from . import restricted
