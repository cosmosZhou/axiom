from util import *


@apply
def apply(ge):
    x, a = ge.of(GreaterEqual)
    return LessEqual(a, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x >= a)

    Eq << Algebra.Le.to.Ge.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-05-24