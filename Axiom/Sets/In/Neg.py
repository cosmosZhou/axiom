from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    return Element(-x, -interval)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq <<= Eq[-2].apply(Algebra.Imply.of.Or), Eq[-1].apply(Algebra.Given.of.Or)

    Eq << Eq[-2].this.args[0].apply(Sets.In.of.In.Neg)

    Eq << Eq[-1].this.args[0].apply(Sets.In.of.In.Neg)




if __name__ == '__main__':
    run()

# created on 2018-10-06
# updated on 2023-05-08
