from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR
    return Element(1 / x, RR)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << Sets.In.to.Any.Eq.apply(Eq[0])

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt_0.to.Lt_0.Div)

    Eq << Eq[-1].this.find(Less).apply(Sets.Lt_0.to.is_negative, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-13
# updated on 2022-04-03
