from util import *


@apply
def apply(lt, le):
    a, x = lt.of(Less)
    _x, b = le.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < a, b <= x)

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-01-04