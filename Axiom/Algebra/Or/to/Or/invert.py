from util import *



@apply
def apply(given, pivot=0):
    [*or_eqs] = given.of(Or)

    precondition = or_eqs[pivot]
    del or_eqs[pivot]
    statement = Or(*or_eqs)

    return Or(precondition, precondition.invert() & statement)


@prove
def prove(Eq):
    from Axiom import Algebra
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,))

    f, g = Function(real=True)

    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)), pivot=1)

    Eq << Algebra.Or.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-05
