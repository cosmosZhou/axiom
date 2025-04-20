from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Set.Subset.given.All_Mem.apply(Eq[1])

    Eq << Eq[-1].this.apply(Algebra.All.Is.And.doit.setlimit)

    Eq << Algebra.And.given.And.apply(Eq[-1])

    Eq <<= Set.Mem_Icc.given.And.apply(Eq[-2]), Set.Mem_Icc.given.And.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-10-22
