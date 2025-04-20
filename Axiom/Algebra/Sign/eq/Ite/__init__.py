from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert not x.shape
    assert x.is_extended_real
    return Equal(self, Piecewise((1, x > 0), (-1, x < 0), (0, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x = Symbol(real=True)
    Eq << apply(Sign(x))

    Eq << Eq[0].this.lhs.apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.Ite__IteAnd_Not)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=Equal(x, 0))

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-2])

    Eq << Logic.Imp.given.Imp.subs.Bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.of.Ne_0)

    Eq.lt_zero, Eq.gt_zero = Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.given.Imp.subs.Bool.apply(Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAbs.of.Gt_0)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])

    Eq << Eq.lt_zero.this.rhs.apply(Logic.Cond_Ite.given.And.Imp)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Logic.Imp.flatten)

    Eq << Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAbs.of.Lt_0)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-22

del Abs
from . import Abs
