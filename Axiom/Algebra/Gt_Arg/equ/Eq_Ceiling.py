from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_Arg.to.Eq_Ceiling)
    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_Ceiling.to.Gt_Arg)


if __name__ == '__main__':
    run()
# created on 2018-10-31
