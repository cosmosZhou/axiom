from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Range)
    a = Max(a, _a + 1)
    return Element(y, Range(a, b, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x > c, Element(x, Range(a, b)))

    Eq << sets.el_range.given.et.apply(Eq[2])

    Eq << sets.el_range.imply.et.apply(Eq[1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[0])

    Eq << algebra.ge.ge.imply.ge.max.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-11-12
