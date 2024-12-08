from util import *


@apply
def apply(lt):
    x, a = lt.of(Abs < Expr)
    assert x.is_extended_real
    return And(Less(x, a), Greater(x, -a))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.LtAbs.to.And)

    Eq << Eq[-1].this.lhs.apply(Algebra.LtAbs.of.And)




if __name__ == '__main__':
    run()
# created on 2022-01-07
