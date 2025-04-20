from util import *


@apply
def apply(a_is_positive, b_is_positive):
    a, R = a_is_positive.of(Element)
    RR = Interval.open(0, oo)
    assert R in RR
    b, R = b_is_positive.of(Element)
    assert R in RR
    return Element(a * b, RR)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval.open(0, oo)))

    Eq << Set.Any.Eq.of.Mem.apply(Eq[0], var='a')

    Eq << Set.Any.Eq.of.Mem.apply(Eq[1], var='b')

    Eq << Algebra.Any.And.of.Any.Any.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.EqMul.of.Eq.Eq)

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Gt_0.of.IsPositive, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Gt_0.of.IsPositive)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << Algebra.Any.of.Any.subs.apply(Eq[-1], a * b, c)

    Eq << Eq[-1].this.find(Greater).apply(Set.IsPositive.of.Gt_0, simplify=None)

    Eq << Algebra.Any.of.Any_And.limits_absorb.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2022-04-03

# updated on 2023-05-13
