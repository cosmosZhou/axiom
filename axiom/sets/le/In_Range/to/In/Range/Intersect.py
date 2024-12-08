from util import *


@apply
def apply(le, contains_y):
    y, a = le.of(LessEqual)
    S[y], domain = contains_y.of(Element)
    b, c = domain.of(Range)
    a = Min(c, a + 1)
    return Element(y, Range(b, a, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x <= a, Element(x, Range(b, c)))

    Eq << Sets.In_Range.of.And.apply(Eq[2])

    Eq << Sets.In_Range.to.And.apply(Eq[1])

    Eq << Algebra.Le.to.Lt.relax.apply(Eq[0])
    Eq << Algebra.Lt.Lt.to.Lt.Min.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-11-12
