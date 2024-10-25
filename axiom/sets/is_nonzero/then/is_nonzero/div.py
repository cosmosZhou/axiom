from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert Element(0, domain) == False
    return Element(1 / x, Interval.open(0, oo) | Interval.open(-oo, 0))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo) | Interval.open(-oo, 0)))

    Eq << sets.el_union.then.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(sets.is_negative.then.is_negative.div)

    Eq << Eq[-1].this.args[0].apply(sets.is_positive.then.is_positive.div)





if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-13
