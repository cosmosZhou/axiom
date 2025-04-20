from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(LessEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Set

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a <= b, Element(x, Interval.open(0, oo)))

    Eq << Set.IsPositive.Div.of.IsPositive.apply(Eq[1])

    Eq << Set.LeMul.of.Le.IsPositive.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2021-10-03