from util import *


def of_limited(given, **kwargs):
    limit, R = given.of(Element)
    assert R.is_set

    expr, *limits = limit.of(Limit)
    if kwargs.get('real'):
        assert R == Interval(-oo, oo)
        return expr, *limits

    if kwargs.get('nonzero'):
        b, a = R.of(Union)
        assert b.of(Interval) == (0, oo)
        assert a.of(Interval) == (-oo, 0)
        assert a.right_open and b.left_open
        return expr, *limits

    if kwargs.get('positive'):
        assert R == Interval.open(0, oo)
        return expr, *limits

    if kwargs.get('extended_real'):
        assert R in Interval(-oo, oo, left_open=False, right_open=False)
        return expr, *limits

    return expr, *limits, R


@apply
def apply(given, ε=None, δ=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0) = of_limited(given, real=True)
    A = fn.generate_var(excludes={x}, **fn.type.dict)

    cond = any_all(Equal(given.lhs, A), ε, δ)
    return cond._subs(A, given.lhs)


@prove
def prove(Eq):
    from axiom import sets, calculus

    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Element(Limit[x:oo](f(x)), Reals))

    Eq << sets.el.imply.any.eq.apply(Eq[0], var='A')

    Eq << Eq[-1].this.expr.apply(calculus.eq.imply.any.all.limit_definition.limit)


if __name__ == '__main__':
    run()

# created on 2020-04-07
from . import symbol_subs
