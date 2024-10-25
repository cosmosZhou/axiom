from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    S[a], S[b] = domain.of(Interval)

    return Element(x, Interval(_a, _b, **domain.kwargs))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el_interval.of.et.apply(Eq[-1])

    Eq << sets.el_interval.then.et.apply(Eq[2])

    Eq << algebra.ge.le.then.ge.trans.apply(Eq[-2], Eq[0])
    Eq << algebra.lt.ge.then.lt.trans.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-11-05
