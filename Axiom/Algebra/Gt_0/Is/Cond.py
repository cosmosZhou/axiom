from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    a, b = Symbol(real=True)
    Eq << apply(Bool(a > b) > 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Cond.of.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.given.Cond)




if __name__ == '__main__':
    run()
# created on 2023-11-05
