from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    return Element(-x, -interval)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq <<= Eq[-2].apply(algebra.infer.of.ou), Eq[-1].apply(algebra.assuming.of.ou)

    Eq << Eq[-2].this.args[0].apply(sets.el.of.el.neg)

    Eq << Eq[-1].this.args[0].apply(sets.el.of.el.neg)




if __name__ == '__main__':
    run()

# created on 2018-10-06
# updated on 2023-05-08
