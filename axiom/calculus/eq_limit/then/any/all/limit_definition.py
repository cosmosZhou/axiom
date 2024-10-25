from util import *


@apply
def apply(given, epsilon=None, delta=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    return any_all(given, epsilon, delta)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq << calculus.eq.to.any_all.limit_definition.apply(Eq[0])

    Eq << algebra.cond.iff.then.cond.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-04-04
