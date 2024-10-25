from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return Element(sqrt(b ** 2 - x ** 2), Interval(0, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el_interval.of.et.apply(Eq[1])

    Eq << sets.el.then.le.max.apply(Eq[0])

    Eq << algebra.le.then.le.square.apply(Eq[-1]).reversed

    Eq << algebra.ge.then.ge_zero.apply(Eq[-1])

    Eq << algebra.ge_zero.then.ge_zero.sqrt.apply(Eq[-1])

    Eq << LessEqual(-x ** 2, 0, plausible=True)

    Eq << algebra.le.then.le.add.apply(Eq[-1], Max(abs(a), abs(b)) ** 2)

    Eq << algebra.ge_zero.le.then.le.sqrt.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-08
