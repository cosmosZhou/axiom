from util import *


@apply
def apply(ge, el):
    a, b = ge.of(GreaterEqual)
    x, domain = el.of(Element)
    S[a], S[b] = domain.of(Interval)
    assert not domain.left_open and not domain.right_open
    return Equal(x, a)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(a >= b, Element(x, Interval(a, b)))

    Eq << sets.el_interval.imply.et.apply(Eq[1])

    Eq << algebra.ge.le.imply.le.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.ge.le.imply.eq.apply(Eq[-1], Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
