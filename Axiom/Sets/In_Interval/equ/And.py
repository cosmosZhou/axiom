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
    from Axiom import Algebra, Sets

    x = Symbol(complex=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In_Interval.to.And)

    Eq << Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)


if __name__ == '__main__':
    run()
# created on 2023-04-16