from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(Greater)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a > b, Element(x, Interval.open(0, oo)))

    Eq << Sets.is_positive.to.is_positive.Div.apply(Eq[1])

    Eq << Sets.Gt.is_positive.to.Gt.Mul.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2021-10-03