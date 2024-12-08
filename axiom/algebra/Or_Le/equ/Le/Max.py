from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(LessEqual | LessEqual)
    return LessEqual(x, Max(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, a) | LessEqual(x, b))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_Max.to.Or.Le)

    Eq << Eq[-2].this.rhs.apply(Algebra.Le_Max.of.Or.Le)




if __name__ == '__main__':
    run()
# created on 2022-01-02
