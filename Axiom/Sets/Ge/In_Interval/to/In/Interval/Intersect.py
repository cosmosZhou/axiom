from util import *


@apply
def apply(ge, contains_y):
    y, a = ge.of(GreaterEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Interval)
    a = Max(b, a)
    return Element(y, Interval(a, c, **domain.kwargs))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x >= a, Element(x, Interval(b, c)))

    Eq << Sets.In_Interval.of.And.apply(Eq[2])

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq << Algebra.Ge.Ge.to.Ge.Max.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-04-06
