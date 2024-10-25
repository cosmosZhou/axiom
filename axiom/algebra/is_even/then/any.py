from util import *


@apply
def apply(given, k=None):
    n = given.of(Equal[Expr % 2, 0])
    if k is None:
        k = Symbol(integer=True)

    return Any[k](Equal(n, k * 2))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol(integer=True, given=True)

    r = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 0))

    k = Eq[1].variable

    Eq << algebra.eq.then.any.definition.mod.apply(Eq[0], q=k)


if __name__ == '__main__':
    run()
# created on 2018-05-03
