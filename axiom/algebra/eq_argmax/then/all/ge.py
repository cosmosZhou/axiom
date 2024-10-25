from util import *


@apply
def apply(given):
    (expr, limit), x0 = given.of(Equal[ArgMax])
    return All(GreaterEqual(expr._subs(limit[0], x0), expr), limit)


@prove
def prove(Eq):
    from axiom import algebra

    x, x0 = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMax[x:S](f(x))))

    Eq << algebra.eq.then.eq.argmax.definition.apply(Eq[0])

    Eq << algebra.eq_maxima.then.all.ge.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-04-13
# updated on 2023-11-05
