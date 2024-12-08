from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_nonpositive
    return Less(1 / x, 0, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True, nonpositive=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.Ne_0.to.Lt_0.apply(Eq[0])

    Eq << Algebra.Lt_0.to.Lt_0.Div.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-22
