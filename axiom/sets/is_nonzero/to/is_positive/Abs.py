from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Element(abs(x), Interval.open(0, oo))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Sets.In_Union.to.Or.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0].apply(Sets.is_positive.to.is_positive.Abs, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Sets.is_negative.to.is_positive.Abs, simplify=None)





if __name__ == '__main__':
    run()
# created on 2020-04-16
# updated on 2023-05-12
