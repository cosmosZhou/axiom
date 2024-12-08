from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True)
    Eq << apply(Bool(a > b) > 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.to.Cond)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.of.Cond)




if __name__ == '__main__':
    run()
# created on 2023-11-05
