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
    from axiom import sets

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b)), d)

    Eq << sets.el_range.imply.et.split.range.apply(Eq[1])

    
    Eq << sets.el.imply.el.div.range.apply(Eq[-1], d)
    


if __name__ == '__main__':
    run()
# created on 2023-05-30
