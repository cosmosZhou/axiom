from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, S.Pi)
    return GreaterEqual(sin(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Geometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=Equal(x, 0))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Equal(x, S.Pi))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[::2].apply(Sets.Ne.In.to.In.Complement, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Sets.Ne.In.to.In.Complement)

    Eq << Eq[-1].this.rhs.apply(Geometry.In_Interval.to.Gt_0.Sin)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.to.Ge_0)




if __name__ == '__main__':
    run()
# created on 2020-11-20
# updated on 2023-05-14
