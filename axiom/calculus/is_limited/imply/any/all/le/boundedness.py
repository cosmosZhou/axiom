from util import *


@apply
def apply(given, delta=None, var=None):
    from axiom.calculus.is_limited.imply.any.all.limit_definition import of_limited
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0, dir) = of_limited(given, real=True)

    M = fn.generate_var(excludes={x}, var=var, positive=True, real=True)
    exists = any_all(Equal(given.lhs, S.Zero), M, delta=delta)

    limits = exists.limits + (M,)
    return exists.func(exists.expr, *limits)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    n = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    #x = Symbol(real=True, shape=(n,))
    #x = Symbol(integer=True)
    f = Function(real=True, shape=())
    #x0 = Symbol(real=True, shape=(n,))
    #x0 = oo
    #x0 = -oo
    #a = oo
    #a = -oo
    direction = 1
    Eq << apply(Element(Limit[x:x0:direction](f(x)), Reals), var='M')

    M = Eq[-1].variables[1]
    Eq << calculus.is_limited.imply.any.all.limit_definition.symbol_subs.apply(Eq[0], var='A')

    A = -Eq[-1].expr.expr.lhs.arg.args[0]
    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.imply.et.split.abs)

    Eq << Eq[-1].this.expr.expr.args[0] + A

    Eq << Eq[-1].this.expr.expr.args[1] + A

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.gt.imply.lt.abs.max)

    Eq << algebra.cond.imply.any.subs.apply(Eq[-1], Eq[-1].expr.expr.rhs, M)

    


if __name__ == '__main__':
    run()
# created on 2020-04-09
# updated on 2023-05-20
