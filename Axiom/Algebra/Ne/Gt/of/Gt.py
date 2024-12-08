from util import *


@apply
def apply(ne, gt):
    x, a = ne.of(Unequal)
    S[x], b = gt.of(Greater)
    assert a >= b
    return x > a


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x = Symbol(real=True)
    Eq << apply(Unequal(x, a), x > a - 1)

    Eq << Algebra.Gt.to.Ne.apply(Eq[2])

    Eq << Algebra.Gt.to.Gt.relax.apply(Eq[2], a - 1)


if __name__ == '__main__':
    run()
# created on 2023-04-13
