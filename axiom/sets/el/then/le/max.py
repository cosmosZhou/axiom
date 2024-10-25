from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return abs(x) <= b


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el_interval.then.et.apply(Eq[0])

    Eq << algebra.le_abs.of.et.apply(Eq[1])

    Eq << algebra.then.le.abs.apply(b)

    Eq << LessEqual(abs(b), Max(abs(a), abs(b)), plausible=True)

    Eq << algebra.le.le.then.le.trans.apply(Eq[-2], Eq[-1])

    Eq << algebra.le.le.then.le.trans.apply(Eq[3], Eq[-1])

    Eq << algebra.then.ge.abs.apply(a)

    Eq << GreaterEqual(-abs(a), -Max(abs(a), abs(b)), plausible=True)

    Eq << algebra.ge.ge.then.ge.trans.apply(Eq[-2], Eq[-1])
    Eq << algebra.ge.ge.then.ge.trans.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-30
