from util import *


@apply
def apply(given, swap=False):
    x, y = given.of(Mul <= 0)
    if swap:
        return x <= 0, y >= 0
    else:
        return x >= 0, y <= 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y <= 0)

    Eq << Algebra.Ge_0.Le_0.to.Le_0.apply(*Eq[1:])




if __name__ == '__main__':
    run()
# created on 2023-04-15