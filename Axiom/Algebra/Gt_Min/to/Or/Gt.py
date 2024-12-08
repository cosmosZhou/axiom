from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr > Min)
    first = args[:index]
    second = args[index:]

    return Greater(x, Min(*first)) | Greater(x, Min(*second))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Min(y, z))

    Eq << Algebra.Lt_Min.to.Or.Lt.apply(Eq[0].reversed)

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].this.args[0].reversed




if __name__ == '__main__':
    run()
# created on 2022-01-02
# updated on 2023-05-20
