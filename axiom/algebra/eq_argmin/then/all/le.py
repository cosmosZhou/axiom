from util import *


@apply
def apply(given):
    (expr, limit), x0 = given.of(Equal[ArgMin])
    return All(LessEqual(expr._subs(limit[0], x0), expr), limit)


@prove
def prove(Eq):
    from axiom import algebra

    x, x0 = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMin[x:S](f(x))))

    Eq << algebra.eq.then.eq.argmin.definition.apply(Eq[0])

    Eq << algebra.eq_minima.then.all.le.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-04-14
# updated on 2023-11-05
