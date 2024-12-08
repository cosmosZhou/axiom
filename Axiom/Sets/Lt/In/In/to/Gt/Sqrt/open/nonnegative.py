from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(0, 1, right_open=True)
    assert domain_y in Interval(0, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(0, 1, right_open=True)), Element(y, Interval(0, 1, right_open=True)))

    Eq << Sets.In_Interval.to.Ge.apply(Eq[1])

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[-1], Eq[0])

    Eq.y_contains = Sets.Gt.In_Interval.to.In.Interval.Intersect.apply(Eq[-1], Eq[2])

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[3], cond=Equal(x, 0))

    Eq <<= Algebra.Imply.of.Imply.subs.apply(Eq[-2]), Algebra.Cond.to.Imply.And.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Sets.Ne.In.to.In.Complement)

    Eq << Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Sets.Lt.In.In.to.Gt.Sqrt.open.positive)


if __name__ == '__main__':
    run()
# created on 2020-11-28
