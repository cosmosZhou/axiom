from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return acos(x) > acos(y)


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry, Sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << Algebra.Gt.of.Gt_0.apply(Eq[3])

    Eq << Geometry.Sin.eq.Sub.apply(sin(Eq[-1].lhs))

    Eq << Sets.Lt.In.In.to.Gt.Sqrt.apply(Eq[0], Eq[1], Eq[2])

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[-1])

    Eq.sin_is_positive = Algebra.Eq.Gt.to.Gt.subs.apply(Eq[-3], Eq[-1])

    Eq << Geometry.Acos.el.Interval.apply(x)

    Eq << Geometry.Acos.el.Interval.apply(y)

    Eq << Sets.In.In.to.In.Sub.Interval.apply(Eq[-2], Eq[-1])

    Eq << Sets.In_Interval.to.Or.apply(Eq[-1], 0, left_open=True)

    Eq << Eq[-1].this.args[1].apply(Geometry.In_Interval.to.Le_0.Sin)

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq.sin_is_positive, Eq[-1])

    Eq << Sets.is_positive.to.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-30
