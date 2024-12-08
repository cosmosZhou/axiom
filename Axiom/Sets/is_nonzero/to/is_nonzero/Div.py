from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert Element(0, domain) == False
    return Element(1 / x, Interval.open(0, oo) | Interval.open(-oo, 0))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo) | Interval.open(-oo, 0)))

    Eq << Sets.In_Union.to.Or.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Sets.is_negative.to.is_negative.Div)

    Eq << Eq[-1].this.args[0].apply(Sets.is_positive.to.is_positive.Div)





if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-13
