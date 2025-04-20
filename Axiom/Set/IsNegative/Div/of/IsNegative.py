from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR
    return Element(1 / x, RR)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << Set.Any.Eq.of.Mem.apply(Eq[0])

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt_0.Div.of.Lt_0)

    Eq << Eq[-1].this.find(Less).apply(Set.IsNegative.of.Lt_0, simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-13
# updated on 2022-04-03
