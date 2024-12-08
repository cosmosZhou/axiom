from util import *


@apply(simplify=False)
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Or(x > 0, x < 0, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True, given=True)
    Eq << apply(Unequal(a, 0))

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.Ge_0.Le_0.to.Eq_0)

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()
# created on 2023-05-02
