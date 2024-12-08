from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(LessEqual)
    return LessEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a <= b, Element(x, Interval.open(0, oo)))

    Eq << Sets.In.to.Any.Eq.apply(Eq[1])

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Gt_0.Le.to.Le.Mul)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2023-05-14
