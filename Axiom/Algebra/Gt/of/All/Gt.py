from util import *


@apply
def apply(gt, var=None):
    from Axiom.Algebra.Le.of.All.Le import all_getitem
    return all_getitem(gt, Greater, var=var)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x > y)

    Eq << Eq[0].this.apply(Algebra.Gt.equ.All.Gt)




if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01
