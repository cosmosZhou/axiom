from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Range)
    a = Max(a, _a + 1)
    return Element(y, Range(a, b, right_open=domain.right_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, x, y = Symbol(integer=True)
    Eq << apply(x > c, Element(x, Range(a, b)))

    Eq << Sets.In_Range.of.And.apply(Eq[2])

    Eq << Sets.In_Range.to.And.apply(Eq[1])

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[0])

    Eq << Algebra.Ge.Ge.to.Ge.Max.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-11-12
