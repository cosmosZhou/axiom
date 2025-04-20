from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    S[0], M = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, M = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, M)))

    Eq << Set.And.of.Mem_Icc.apply(Eq[0])



    Eq << Algebra.LeSquare.of.Ge_0.Le.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-10
