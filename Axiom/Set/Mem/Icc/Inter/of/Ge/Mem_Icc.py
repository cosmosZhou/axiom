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
    from Axiom import Set, Algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x >= a, Element(x, Interval(b, c)))

    Eq << Set.Mem_Icc.given.And.apply(Eq[2])

    Eq << Set.And.of.Mem_Icc.apply(Eq[1])

    Eq << Algebra.GeMax.of.Ge.Ge.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-04-06
