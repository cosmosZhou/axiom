from util import *


@apply
def apply(given):
    from axiom.algebra.all.any.imply.any.all.et import limits_dependent
    fn, *limits = given.of(All)
    assert len(limits) == 2
    limit_x, limit_y = limits

    limits = limit_y, limit_x

    assert not limits_dependent([limit_x], [limit_y])

    return All(fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    f, g = Function(integer=True)

    Eq << apply(All[x:g(x) > 0, y:g(y) > 0](f(x, y) > 0))

    Eq << algebra.all.imply.ou.apply(Eq[0])

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=x)

    Eq << Eq[-1].this.expr.apply(algebra.ou.imply.all, pivot=1, wrt=y)


if __name__ == '__main__':
    run()

# created on 2018-12-14
