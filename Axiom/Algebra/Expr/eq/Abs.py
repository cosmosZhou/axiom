from util import *


@apply
def apply(self):
    assert self >= 0
    return Equal(self, Abs(self, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, nonnegative=True)
    Eq << apply(x)

    Eq << Eq[0].this.rhs.apply(Algebra.Abs.eq.Piece)




if __name__ == '__main__':
    run()
# created on 2023-04-03
