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
    from Axiom import Set, Algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x <= a, Element(x, Interval(b, c)))

    Eq << Set.Mem_Icc.given.And.apply(Eq[2])

    Eq << Set.And.of.Mem_Icc.apply(Eq[1])

    Eq << Algebra.LeMin.of.Le.Le.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-11-27
