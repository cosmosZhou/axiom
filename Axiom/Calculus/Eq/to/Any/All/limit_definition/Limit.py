from util import *


@apply
def apply(given, ε=None, δ=None):
    from Axiom.Calculus.Eq.equ.Any_All.limit_definition import Any_All
    cond = Any_All(given, ε, δ)
    new, old = given.args
    return cond._subs(old, new)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq << Calculus.Eq.equ.Any_All.limit_definition.apply(Eq[0])

    Eq << Algebra.Cond.Iff.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2020-04-07
