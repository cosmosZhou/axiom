from util import *


@apply
def apply(ge, contains_y):
    y, a = ge.of(GreaterEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Range)
    a = Max(b, a)
    return Element(y, Range(a, c, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x >= a, Element(x, Range(b, c)))

    Eq << sets.el_range.given.et.apply(Eq[2])

    Eq << sets.el_range.imply.et.apply(Eq[1])

    Eq << algebra.ge.ge.imply.ge.max.apply(Eq[-1], Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-11-12
