from util import *



@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, a = Symbol(integer=True, given=True)

    Eq << apply(abs(x) < a)

    Eq << Algebra.Lt.Gt.to.Lt.Abs.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-18
