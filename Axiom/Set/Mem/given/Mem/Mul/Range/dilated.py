from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])

    e *= d

    return Element(e, Range(a * d, (b - 1) * d + 1, d))


@prove
def prove(Eq):
    from Axiom import Set

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b)), d)

    Eq << Set.And.of.Mem_Range.split.Range.apply(Eq[1])


    Eq << Set.Mem.Div.Range.of.Mem.apply(Eq[-1], d)



if __name__ == '__main__':
    run()
# created on 2023-05-30
