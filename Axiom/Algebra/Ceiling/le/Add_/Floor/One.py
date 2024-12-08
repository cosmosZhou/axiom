from util import *


@apply
def apply(x):
    return LessEqual(Ceiling(x), floor(x) + 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << Algebra.Ceiling.lt.Add_1.apply(x)

    Eq << Algebra.Lt.to.Le.Floor.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-10-02
