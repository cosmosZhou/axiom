from util import *


@apply
def apply(imply):
    e, S = imply.of(Element)
    a, b = S.of(Interval)
    assert not S.left_open
    return Element(e, Interval(a, b, right_open=S.right_open, left_open=True))


@prove
def prove(Eq):
    from axiom import sets
    
    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))
    Eq << sets.el.imply.el.left_close.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-02-28
# updated on 2021-02-28
