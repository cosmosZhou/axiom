from util import *


@apply
def apply(ge, contains_y):
    y, a = ge.of(GreaterEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Range)
    a = Max(b, a)
    return Element(y, Range(a, c, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x >= a, Element(x, Range(b, c)))

    Eq << Sets.In_Range.of.And.apply(Eq[2])

    Eq << Sets.In_Range.to.And.apply(Eq[1])

    Eq << Algebra.Ge.Ge.to.Ge.Max.apply(Eq[-1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-11-12
