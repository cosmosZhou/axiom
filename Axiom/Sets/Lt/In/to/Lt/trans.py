from util import *


@apply
def apply(lt, contains_y):
    y, domain_y = contains_y.of(Element)
    a, b = domain_y.of(Interval)
    x, S[y] = lt.of(Less)
    return x < b


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(x < y, Element(y, Interval(a, b)))

    Eq << Sets.In_Interval.to.Le.apply(Eq[1])

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-25
