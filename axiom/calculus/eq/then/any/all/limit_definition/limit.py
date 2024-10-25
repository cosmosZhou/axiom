from util import *


@apply
def apply(given, ε=None, δ=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    cond = any_all(given, ε, δ)
    new, old = given.args
    return cond._subs(old, new)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq << calculus.eq.to.any_all.limit_definition.apply(Eq[0])

    Eq << algebra.cond.iff.then.cond.trans.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2020-04-07
