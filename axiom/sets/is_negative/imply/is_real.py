from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(-oo, 0)
    return Element(x, Reals)


@prove
def prove(Eq):
    from axiom import sets
    
    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))
    
    Eq << sets.el.imply.eq.definition.apply(Eq[0])
    
    Eq << Eq[1].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2023-05-03
