from util import *


@apply
def apply(given):
    x, (a, b) = given.of(Element[Range])

    return LessEqual(x, b - 1)


@prove
def prove(Eq):
    from Axiom import Sets
    x = Symbol(real=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Subset(Eq[0].rhs, Interval(-oo, b - 1), plausible=True)

    Eq << Sets.In.Subset.to.In.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-04
