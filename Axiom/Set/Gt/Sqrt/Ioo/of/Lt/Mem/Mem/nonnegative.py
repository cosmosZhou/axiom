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
    from Axiom import Set, Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(0, 1, right_open=True)), Element(y, Interval(0, 1, right_open=True)))

    Eq << Set.Ge.of.Mem_Icc.apply(Eq[1])

    Eq << Algebra.Gt.of.Ge.Lt.apply(Eq[-1], Eq[0])

    Eq.y_contains = Set.Mem.Icc.Inter.of.Gt.Mem_Icc.apply(Eq[-1], Eq[2])

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[3], cond=Equal(x, 0))

    Eq <<= Logic.Imp.given.Imp.subs.apply(Eq[-2]), Logic.Imp.And.of.Cond.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Logic.Imp.given.Cond.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Set.Mem_SDiff.of.Mem.Ne)

    Eq << Logic.Imp.And.of.Cond.Imp.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Set.Gt.Sqrt.Ioo.of.Lt.Mem.Mem.positive)


if __name__ == '__main__':
    run()
# created on 2020-11-28
