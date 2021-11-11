from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(Less)
    b, _x = _greater_than.of(Less)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    assert x == _x
    assert x.is_integer
    return Element(x, Range(b + 1, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(integer=True, given=True)
    Eq << apply(b < x, x < a)

    #Eq << apply(x < b, a <= x)
    Eq << sets.el.given.et.split.range.apply(Eq[-1])



    Eq << algebra.ge.given.gt.apply(Eq[-1])

    Eq << Eq[-1].reversed

    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-06-02
# updated on 2021-06-02