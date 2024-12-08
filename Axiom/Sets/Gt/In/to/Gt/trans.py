from util import *


@apply
def apply(gt, contains_y):
    y, domain_y = contains_y.of(Element)
    a, b = domain_y.of(Interval)
    x, S[y] = gt.of(Greater)
    return x > a


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(x > y, Element(y, Interval(a, b)))

    Eq << Sets.In_Interval.to.Ge.apply(Eq[1])

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-25
