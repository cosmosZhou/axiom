from util import *


@apply
def apply(lt):
    x, a = lt.of(Abs < Expr)
    assert x.is_extended_real
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << Algebra.LtAbs.to.Lt.apply(Eq[0])

    Eq << Algebra.LtAbs.to.Gt.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-07-28
# updated on 2022-01-07