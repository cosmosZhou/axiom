from util import *


@apply
def apply(given, k=None):
    n = given.of(Unequal[Expr % 2, 0])
    if k is None:
        k = Symbol(integer=True)

    return Any[k](Equal(n, k * 2 + 1))


@prove
def prove(Eq):
    from Axiom import Algebra
#     n = q * d + r
    n = Symbol(integer=True, given=True)

    r = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << Algebra.Ne_0.to.Eq_odd.apply(Eq[0])

    Eq << Algebra.Eq_odd.to.Any.apply(Eq[-1], k=Eq[1].variable)


if __name__ == '__main__':
    run()
# created on 2019-05-10