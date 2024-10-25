from util import *


@apply
def apply(le, contains_y):
    y, a = le.of(LessEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Interval)
    a = Min(c, a)
    return Element(y, Interval(b, a, **domain.kwargs))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x <= a, Element(x, Interval(b, c)))

    Eq << sets.el_interval.of.et.apply(Eq[2])

    Eq << sets.el_interval.then.et.apply(Eq[1])

    Eq << algebra.le.le.then.le.min.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-11-27
