from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return And(x > a, x < b)
        else:
            return And(x > a, x <= b)
    else:
        if interval.right_open:
            return And(x >= a, x < b)
        else:
            return And(x >= a, x <= b)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.And.of.Mem_Icc, simplify=False)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Icc.of.Le.Ge)


if __name__ == '__main__':
    run()

# created on 2021-03-26
