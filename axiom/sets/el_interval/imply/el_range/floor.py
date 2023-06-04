from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    a, b = domain.of(Interval)
    assert domain.right_open
    if domain.left_open:
        assert a.is_infinite
    else:
        if not a.is_integer:
            a = Floor(a)

    if not b.is_integer:
        b = Ceiling(b)

    return Element(Floor(x), Range(a, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.el_interval.imply.el_range.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.neg.floor)

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    Eq << Eq[-1].this.find(-~Ceiling).apply(algebra.ceiling.to.neg.floor)

    Eq << Eq[-1].this.find(-~Floor).apply(algebra.floor.to.neg.ceiling)




if __name__ == '__main__':
    run()
# created on 2021-03-05
# updated on 2023-04-17
