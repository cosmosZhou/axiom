from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    assert x.is_finite
    return Element(log(x), Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    f = Function(complex=True)
    Eq << apply(f(x) > 0)

    Eq << sets.gt_zero.then.is_positive.apply(Eq[0], simplify=None)

    Eq << sets.el.then.eq.definition.apply(Eq[-1], 'y')

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-04-17
