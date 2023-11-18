from util import *


@apply
def apply(is_negative, gt):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)
    
    lhs, rhs = gt.of(Greater)

    return Less(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import sets, algebra
    
    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Greater(g(x), h(x)))
    
    Eq << sets.is_negative.imply.lt_zero.apply(Eq[0])
    
    Eq << algebra.lt_zero.gt.imply.lt.div.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15
