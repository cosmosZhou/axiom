from util import *


@apply
def apply(el, n):
    x, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.left_open and domain.right_open
    return Equal(Limit[n:oo](x ** n), ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(0, 1, left_open=True, right_open=True)), n)

    Eq << Calculus.Eq_Limit.of.Any_All.limit_definition.restricted.apply(Eq[1])

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.of.Lt.Log)

    Eq.gt_zero = Sets.In_Interval.to.Gt.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Gt_0.to.Eq.Log.apply(Eq.gt_zero, Eq[-1].find(All).variable)

    Eq.any = Eq[-2].subs(Eq[-1])

    Eq.lt_zero = Sets.In_Interval.to.Lt_0.Log.apply(Eq[0])

    Eq << Element(Eq.any.find(Mul < ~Log), Interval.open(-oo, 0), plausible=True)

    Eq << Sets.Lt_0.In.to.In.Div.apply(Eq.lt_zero, Eq[-1], simplify=None)

    Eq.Ceiling_el = Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])

    Eq << Algebra.Any.of.Cond.subs.apply(Eq.any, Eq.any.variable, Eq.Ceiling_el.lhs)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Algebra.GeCeiling.apply(Eq.Ceiling_el.lhs.arg)

    Eq << Algebra.Ge.to.Gt.relax.apply(Eq[-1], step=1)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.Gt.to.Gt.trans)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq.lt_zero, Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.Gt.to.Lt.Mul)





if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-11-05
