from util import *


@apply
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    return And(LessEqual(x, a), GreaterEqual(x, -a))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.LeAbs.to.And)

    Eq << Eq[-1].this.lhs.apply(Algebra.LeAbs.of.And)




if __name__ == '__main__':
    run()
# created on 2022-01-07
