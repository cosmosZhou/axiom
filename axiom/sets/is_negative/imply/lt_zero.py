from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(-oo, 0, right_open=True)
    assert x.is_extended_complex
    return x < 0


@prove
def prove(Eq):
    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]

    


if __name__ == '__main__':
    run()

# created on 2020-04-10
# updated on 2023-04-18
