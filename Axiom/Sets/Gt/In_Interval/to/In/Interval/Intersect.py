from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Interval)
    a = Max(a, _a)
    return Element(y, Interval(a, b, left_open=True, right_open=domain.right_open))


@prove
def prove(Eq):
    from Axiom import Sets

    a, b, x, y = Symbol(real=True)
    Eq << apply(x > a, Element(x, Interval(a, b)))

    Eq << Sets.In_Interval.of.And.apply(Eq[2])

    Eq << Sets.In_Interval.to.And.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-06-21
