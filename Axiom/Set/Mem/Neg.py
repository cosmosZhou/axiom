from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    return Element(-x, -interval)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].apply(Logic.Imp.given.Or_Not), Eq[-1].apply(Algebra.Given.given.Or)

    Eq << Eq[-2].this.args[0].apply(Set.Mem.given.Mem.Neg)

    Eq << Eq[-1].this.args[0].apply(Set.Mem.given.Mem.Neg)




if __name__ == '__main__':
    run()

# created on 2018-10-06
# updated on 2023-05-08
