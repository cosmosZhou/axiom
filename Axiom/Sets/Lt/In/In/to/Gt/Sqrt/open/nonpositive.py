from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 0, left_open=True)
    assert domain_y in Interval(-1, 0, left_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 0, left_open=True)), Element(y, Interval(-1, 0, left_open=True)))

    Eq << -Eq[0].reversed

    Eq << Sets.In.to.In.Neg.apply(Eq[1])

    Eq << Sets.In.to.In.Neg.apply(Eq[2])
    Eq << Sets.Lt.In.In.to.Gt.Sqrt.open.nonnegative.apply(Eq[-3], Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-11-28