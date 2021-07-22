from util import *


@apply
def apply(given, *limits):

    function, *limits_f = given.of(All)

    variables_set = given.variables_set
    for var, *ab in limits:
        assert var not in variables_set

    limits = tuple(limits_f) + limits
    return All(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(real=True)

    Eq << apply(All[x:A](f(x, y) > 0), (y, B))

    Eq << Eq[0].this.expr.apply(algebra.cond.imply.all.restrict, (y, B))

    Eq << algebra.all.imply.all.limits.swap.apply(Eq[-1])


if __name__ == '__main__':
    run()

