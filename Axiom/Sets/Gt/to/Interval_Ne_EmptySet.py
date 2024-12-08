from util import *


@apply
def apply(given, x=None, left_open=True, right_open=True):
    b, a = given.of(Greater)
    if x is None:
        x = given.generate_var(var='x', real=True)

    assert left_open or right_open
    return Unequal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(b > a)

    Eq << Sets.Lt.to.Any_In.Interval.apply(Eq[0].reversed)

    Eq << Sets.Any_In.to.Ne_EmptySet.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-17
