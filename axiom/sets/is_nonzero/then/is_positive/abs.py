from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Element(abs(x), Interval.open(0, oo))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << sets.el_union.then.ou.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.is_positive.then.is_positive.abs, simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.is_negative.then.is_positive.abs, simplify=None)





if __name__ == '__main__':
    run()
# created on 2020-04-16
# updated on 2023-05-12
