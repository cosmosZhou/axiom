from util import *


@apply
def apply(given, reverse=False):
    x, R = given.of(Element)
    assert R in Reals
    if reverse:
        return Equal(x, ~x)
    return Equal(~x, x)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(-oo, oo)))

    Eq << sets.el.then.eq.definition.apply(Eq[0])

    Eq << algebra.eq.then.eq.conj.apply(Eq[-1])

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-23
