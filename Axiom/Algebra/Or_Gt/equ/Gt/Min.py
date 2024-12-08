from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(Greater | Greater)
    return Greater(x, Min(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(x, a) | Greater(x, b))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_Min.to.Or.Gt)

    Eq << Eq[-2].this.rhs.apply(Algebra.Gt_Min.of.Or.Gt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
