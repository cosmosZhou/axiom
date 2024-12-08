from util import *


@apply
def apply(given):
    x = given.of(Equal[Floor, 0])
    return Element(x, Interval(0, 1, right_open=True))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(Floor(x), 0))

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Algebra.Ge_Floor.apply(x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Algebra.Lt_Add_.Floor.One.apply(x)

    Eq << Eq[-1].subs(Eq[0])






if __name__ == '__main__':
    run()
# created on 2020-01-19
