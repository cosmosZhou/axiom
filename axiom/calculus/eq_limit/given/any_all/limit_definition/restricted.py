from util import *


@apply
def apply(given, epsilon=None, delta=None, upper=1):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    upper = sympify(upper)
    return any_all(given, epsilon, delta, upper)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, a = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Equal(Limit[x:oo](f(x)), a))

    Eq.all = algebra.cond.imply.all.apply(Eq[1], Eq[1].find(Abs < ~Symbol))

    ε = Eq.all.variable
    Eq << All(Eq.all.expr, (ε, Interval(1, oo)), plausible=True)

    Eq << algebra.all.given.et.all.split.apply(Eq[-1], cond=ε > 1)

    Eq << algebra.all.imply.cond.subs.apply(Eq.all, ε, S.One / 2)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.imply.lt.relax, 1)

    χ = Symbol(domain=Interval.open(1, oo))
    Eq << algebra.all.imply.cond.subs.apply(Eq.all, ε, 1 / χ)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.imply.lt.relax, χ)

    Eq << algebra.cond.imply.all.apply(Eq[-1], χ)

    Eq <<= Eq.all & Eq[2]

    Eq << calculus.eq_limit.given.any_all.limit_definition.apply(Eq[0])

    Eq << algebra.cond.given.all.apply(Eq[-1], Eq[-1].find(Abs < ~Symbol))

    


if __name__ == '__main__':
    run()
# created on 2023-04-17
