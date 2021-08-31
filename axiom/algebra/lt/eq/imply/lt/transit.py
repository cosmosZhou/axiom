from util import *


def swap(cls, cond, eq):
    a, x = cond.of(cls)
    b, _x = eq.of(Equal)
    if a == _x:
        a, b, x = b, x, a
    elif a == b:
        a, b, x, _x = _x, x, a, b
    elif x == b:
        _x, b = b, _x
    assert x == _x
    return a, b


@apply
def apply(lt, eq):
    return Less(*swap(Less, lt, eq))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a < x, Equal(b, x))
    # Eq << apply(a < x, Equal(x, b))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(algebra.lt.simplify.common_terms)


if __name__ == '__main__':
    run()
