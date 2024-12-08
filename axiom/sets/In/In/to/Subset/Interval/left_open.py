from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)
    a, b = A.of(Interval)
    return Subset(Interval(x, y, left_open=True), Interval(a, b, right_open=A.right_open, left_open=True))


@prove
def prove(Eq):
    from Axiom import Sets

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, right_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << Sets.In.In.to.Subset.Interval.apply(Eq[0], Eq[1])

    Eq << Sets.Subset.to.Subset.Complement.apply(Eq[-1], {x})

    Eq << Sets.In.to.Eq.Complement.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.subset = Sets.Subset.to.Subset.Complement.apply(Eq[-1], Eq[-1].rhs.args[1])

    Eq << Sets.In_Interval.to.Le.apply(Eq[0])

    Eq << Sets.Le.to.Subset.Interval.oo.apply(Eq[-1], left_open=True)

    Eq << Sets.Subset.to.Subset.Intersect.apply(Eq[-1], Interval.open(-oo, b))

    Eq << Sets.Subset.Subset.to.Subset.trans.apply(Eq.subset, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2021-02-27
# updated on 2023-05-04
