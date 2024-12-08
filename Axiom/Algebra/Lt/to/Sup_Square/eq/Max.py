from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Max(m ** 2, M ** 2))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq << Element(x, Interval(m, M, left_open=True, right_open=True)).this.apply(Sets.In_Interval.to.Lt.Square)

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Algebra.All_Lt.to.LeSup.apply(Eq[-1])

    Eq << Algebra.GeSup.of.All_Any_Gt.apply(Eq[3], 'U')

    Eq << Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.Lt_Max.to.Any.GtSquare)


if __name__ == '__main__':
    run()
# created on 2019-09-08
