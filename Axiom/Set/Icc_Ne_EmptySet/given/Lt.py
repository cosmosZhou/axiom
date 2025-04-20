from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return Less(a, b)


@prove
def prove(Eq):
    from Axiom import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b, left_open=True), a.emptySet))

    Eq << Set.Icc_Ne_EmptySet.of.Lt.apply(Eq[1], right_open=False)




if __name__ == '__main__':
    run()
# created on 2021-05-10
