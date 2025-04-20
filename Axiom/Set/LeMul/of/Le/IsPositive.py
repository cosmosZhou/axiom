from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(LessEqual)
    return LessEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a <= b, Element(x, Interval.open(0, oo)))

    Eq << Set.Any.Eq.of.Mem.apply(Eq[1])

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.LeMul.of.Gt_0.Le)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2023-05-14
