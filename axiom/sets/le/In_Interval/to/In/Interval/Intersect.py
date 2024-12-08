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
    from Axiom import Sets, Algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x <= a, Element(x, Interval(b, c)))

    Eq << Sets.In_Interval.of.And.apply(Eq[2])

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq << Algebra.Le.Le.to.Le.Min.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-11-27
