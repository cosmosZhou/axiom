from util import *


@apply
def apply(given):
    [*args], x = given.of(Equal[Min])
    assert x in args
    args.remove(x)
    return x <= Max(*args)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True)
    Eq << apply(Equal(x, Min(x, y)))

    Eq << Algebra.Le.to.Eq.Min.apply(Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-03-26