from util import *


@apply
def apply(ne, le):
    x, a = ne.of(Unequal)
    S[x], b = le.of(LessEqual)
    assert a < b
    return x < a


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x = Symbol(real=True)
    Eq << apply(Unequal(x, a), x <= a + 1)

    Eq << Algebra.Lt.to.Ne.apply(Eq[2])

    Eq << Algebra.Lt.to.Le.relax.apply(Eq[2])

    Eq << Algebra.Le.to.Le.relax.apply(Eq[-1], a + 1)


if __name__ == '__main__':
    run()
# created on 2023-04-13
