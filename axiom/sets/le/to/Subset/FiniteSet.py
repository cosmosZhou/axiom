from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Sets.Subset.of.All_In.apply(Eq[1])

    Eq << Eq[-1].this.apply(Algebra.All.equ.And.doit.setlimit)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= Sets.In_Interval.of.And.apply(Eq[-2]), Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-10-22
