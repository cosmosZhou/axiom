from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return Element(sqrt(b ** 2 - x ** 2), Interval(0, b))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq << Sets.In.to.Le.Max.apply(Eq[0])

    Eq << Algebra.Le.to.Le.Square.apply(Eq[-1]).reversed

    Eq << Algebra.Ge.to.Ge_0.apply(Eq[-1])

    Eq << Algebra.Ge_0.to.Ge_0.Sqrt.apply(Eq[-1])

    Eq << LessEqual(-x ** 2, 0, plausible=True)

    Eq << Algebra.Le.to.Le.Add.apply(Eq[-1], Max(abs(a), abs(b)) ** 2)

    Eq << Algebra.Ge_0.Le.to.Le.Sqrt.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-08
