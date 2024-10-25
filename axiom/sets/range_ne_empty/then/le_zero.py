from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(a - b, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << sets.range_ne_empty.then.le.apply(Eq[0])

    Eq << algebra.le.then.le_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-23
