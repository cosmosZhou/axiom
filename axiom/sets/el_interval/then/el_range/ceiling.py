from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert domain.left_open
    if domain.right_open:
        assert b.is_infinite
    else:
        if not b.is_integer:
            b = Ceiling(b)

    if not a.is_integer:
        a = Floor(a)
    return Element(Ceiling(x), Range(a + 1, b + 1))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << sets.el.then.el.relax.interval.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(sets.interval.to.cup.left_open)

    Eq << sets.el_cup.then.any_el.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el.then.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(sets.eq.then.el.finiteset)

    Eq << sets.any_el.then.el.cup.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.subs.offset, -1)




if __name__ == '__main__':
    run()
# created on 2018-10-24
# updated on 2023-04-17
