from util import *


@apply
def apply(self):
    assert self >= 0
    return Equal(self, Abs(self, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, nonnegative=True)
    Eq << apply(x)

    Eq << Eq[0].this.rhs.apply(algebra.abs.to.piece)




if __name__ == '__main__':
    run()
# created on 2023-04-03
