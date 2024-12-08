from util import *


@apply
def apply(is_real):
    x, C = is_real.of(Element)
    assert C in Reals
    return Element(x ** 2, Interval(0, oo))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(super_real=True)
    Eq << apply(Element(x, Reals))

    Eq << Sets.is_real.is_real.to.is_real.apply(Eq[0], Eq[0])

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq << Sets.is_real.to.Eq.Square.Abs.apply(Eq[0])

    Eq <<= Eq[1].subs(Eq[-1].reversed), Eq[2].subs(Eq[-1].reversed)


    Eq <<= Sets.In_Interval.of.And.apply(Eq[-2]),Sets.In_Interval.to.And.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-06-29
