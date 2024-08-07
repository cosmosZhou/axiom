from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b, d = domain.of(Range)
    assert x.is_integer
    return Element(x, Range(a, b, sign(d))), Equal(x % d, a % d)

@prove
def prove(Eq):
    from axiom import sets, algebra
    
    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b, d)))
    
    Eq << Eq[0].this.apply(sets.el_range.to.et.split.range)
    
    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-30
