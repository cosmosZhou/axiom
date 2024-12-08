from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    R = Interval.open(0, oo)
    assert domain in R
    return Element(1 / x, R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Sets.In.to.Any.Eq.apply(Eq[0])

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.to.Gt_0.Div)

    Eq << Eq[-1].this.find(Greater).apply(Sets.Gt_0.to.is_positive, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-03
