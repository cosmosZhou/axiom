from util import *


@apply
def apply(given, negate=False):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    if negate:
        x = -x
    assert x.is_extended_real
    return Less(x, a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << Algebra.Le_Abs.apply(x)

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-07-27
# updated on 2023-04-16
