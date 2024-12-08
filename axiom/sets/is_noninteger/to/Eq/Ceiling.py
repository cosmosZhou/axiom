from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])
    return Equal(ceiling(x), floor(x) + 1)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Algebra.GeCeiling.apply(x)

    Eq << Sets.NotIn.to.Gt_0.Frac.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Frac.eq.Add)

    Eq << Algebra.Gt_0.to.Gt.apply(Eq[-1])

    Eq.lt_floor = Eq[-1].reversed

    Eq << Algebra.Ge.Gt.to.Gt.trans.apply(Eq[2], Eq[-1])

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])

    Eq.gt_floor = Algebra.Floor.gt.Sub_1.apply(x)

    Eq << Eq.gt_floor + 1

    Eq << Algebra.Ge.Gt.to.Gt.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Ceiling.lt.Add_1.apply(x)

    Eq << Sets.Gt.Lt.to.In.Interval.apply(Eq[-1], Eq[-2])

    Eq << Sets.Gt.Lt.to.In.Interval.apply(Eq.gt_floor, Eq.lt_floor)

    Eq << Sets.In.In.to.In.Sub.Interval.apply(Eq[-2], Eq[-1])

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq <<= Algebra.Gt.to.Ge.strengthen.apply(Eq[-2]), Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Ge.Le.to.Eq.apply(Eq[-1], Eq[-2])
    Eq << Eq[-1].this.apply(Algebra.Eq.transport)


if __name__ == '__main__':
    run()
# created on 2018-05-17
