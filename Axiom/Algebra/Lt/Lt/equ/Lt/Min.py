from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.Lt.to.Lt.Min)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt.Lt.of.Lt.Min)




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
