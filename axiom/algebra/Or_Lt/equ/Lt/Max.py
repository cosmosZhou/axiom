from util import *


@apply
def apply(given):
    (x, a), (S[x], b) = given.of(Less | Less)
    return Less(x, Max(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Less(x, a) | Less(x, b))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt_Max.to.Or.Lt)

    Eq << Eq[-2].this.rhs.apply(Algebra.Lt_Max.of.Or.Lt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
