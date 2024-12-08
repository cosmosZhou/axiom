from util import *


@apply
def apply(given):
    x = given.of(Equal[Ceiling, 0])
    return Element(x, Interval(-1, 0, left_open=True))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(Ceiling(x), 0))

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Algebra.Le_Ceiling.apply(x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-12
