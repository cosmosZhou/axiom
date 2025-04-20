from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, S.Pi, left_open=True, right_open=True)
    return Greater(sin(x), 0)


@prove(proved=False)
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi, left_open=True, right_open=True)))

    Eq << Geometry.Sin.eq.Sum.apply(sin(x))




















if __name__ == '__main__':
    run()
# created on 2020-11-19
