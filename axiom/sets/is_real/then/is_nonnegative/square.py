from util import *


@apply
def apply(is_real):
    x, C = is_real.of(Element)
    assert C in Reals
    return Element(x ** 2, Interval(0, oo))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(super_real=True)
    Eq << apply(Element(x, Reals))

    Eq << sets.is_real.is_real.then.is_real.apply(Eq[0], Eq[0])

    Eq << sets.el_interval.then.et.apply(Eq[-1])

    Eq << sets.is_real.then.eq.square.abs.apply(Eq[0])

    Eq <<= Eq[1].subs(Eq[-1].reversed), Eq[2].subs(Eq[-1].reversed)


    Eq <<= sets.el_interval.of.et.apply(Eq[-2]),sets.el_interval.then.et.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-06-29
