from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    assert interval in Interval(1, oo)
    return log(x) >= 0


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(f(x), Interval(1, oo)))

    Eq << sets.el.then.eq.definition.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << sets.el_interval.then.ge.apply(Eq[0])

    Eq << algebra.ge.then.gt.relax.apply(Eq[-1], 0)

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-17
