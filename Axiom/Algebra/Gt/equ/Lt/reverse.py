from util import *


@apply
def apply(gt):
    x, a = gt.of(Greater)
    return Less(a, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x > a)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-02
