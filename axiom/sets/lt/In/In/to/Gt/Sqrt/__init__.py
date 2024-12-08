from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << Sets.Lt.In.to.Lt.trans.apply(Eq[0], Eq[2])

    Eq.x_contains = Sets.Lt.In_Interval.to.In.Interval.Intersect.apply(Eq[-1], Eq[1])

    Eq << Sets.Gt.In.to.Gt.trans.apply(Eq[0].reversed, Eq[1])

    Eq.y_contains = Sets.Gt.In_Interval.to.In.Interval.Intersect.apply(Eq[-1], Eq[2])

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[3], cond=Equal(x, -1))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << -Sets.In.to.Lt.Square.apply(Eq.y_contains) + 1

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.apply(Eq.x_contains, cond=Eq[-4].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Ne.In.to.In.Complement)

    Eq << Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Sets.Lt.In.In.to.Gt.Sqrt.open)


if __name__ == '__main__':
    run()
# created on 2020-11-29
from . import open
