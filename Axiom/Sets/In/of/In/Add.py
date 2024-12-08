from util import *


@apply
def apply(imply, c):
    e, interval = imply.of(Element)
    assert c.is_finite

    return Element(e + c, interval + c)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(complex=True)
    a, b, c = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), c=c)

    Eq << Sets.In_Interval.to.Le.apply(Eq[1])

    Eq << Sets.In_Interval.to.Ge.apply(Eq[1])

    Eq << Sets.In_Interval.of.And.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-02-26
