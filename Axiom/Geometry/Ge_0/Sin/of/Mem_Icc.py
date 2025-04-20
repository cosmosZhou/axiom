from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, S.Pi)
    return GreaterEqual(sin(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Geometry, Logic

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi)))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=Equal(x, 0))

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-2])

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=Equal(x, S.Pi))

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-2])

    Eq << Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[::2].apply(Set.Mem_SDiff.of.Mem.Ne, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Set.Mem_SDiff.of.Mem.Ne)

    Eq << Eq[-1].this.rhs.apply(Geometry.Gt_0.Sin.of.Mem_Icc)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.of.Gt_0)




if __name__ == '__main__':
    run()
# created on 2020-11-20
# updated on 2023-05-14
