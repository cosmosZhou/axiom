from util import *


@apply
def apply(self):
    x, interval = self.of(Element)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            rhs = x > a, x < b
        else:
            rhs = x > a, x <= b
    else:
        if interval.right_open:
            rhs = x >= a, x < b
        else:
            rhs = x >= a, x <= b

    rhs = And(*rhs)
    return rhs


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(complex=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_interval.then.et)

    Eq << Eq[-1].this.rhs.apply(sets.el_interval.of.et)


if __name__ == '__main__':
    run()
# created on 2023-04-16
