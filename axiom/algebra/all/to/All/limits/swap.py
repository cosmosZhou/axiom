from util import *


@apply
def apply(given):
    from Axiom.Algebra.All.Any.to.Any.All.And import limits_dependent
    fn, *limits = given.of(All)
    assert len(limits) == 2
    limit_x, limit_y = limits

    limits = limit_y, limit_x

    assert not limits_dependent([limit_x], [limit_y])

    return All(fn, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)
    f, g = Function(integer=True)

    Eq << apply(All[x:g(x) > 0, y:g(y) > 0](f(x, y) > 0))

    Eq << Algebra.All.to.Or.apply(Eq[0])

    Eq << Algebra.Or.to.All.apply(Eq[-1], pivot=1, wrt=x)

    Eq << Eq[-1].this.expr.apply(Algebra.Or.to.All, pivot=1, wrt=y)


if __name__ == '__main__':
    run()

# created on 2018-12-14
