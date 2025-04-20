from util import *


@apply
def apply(given, x=None):
    a, b = given.of(Less)
    if x is None:
        x = given.generate_var(var='x', integer=True)

    return Any[x](Element(x, Range(a, b)))


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    a, b = Symbol(integer=True, given=True)
    Eq << apply(a < b)

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[0]) + 1

    x = Eq[1].variable
    Eq << Algebra.Any.given.Cond.subs.apply(Eq[1], x, b - 1)

    Eq << Set.Mem_Range.given.And.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2021-04-18
