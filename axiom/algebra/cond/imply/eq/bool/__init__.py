from util import *



@apply
def apply(given):
    assert given.is_bool
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    f = Function(shape=(), real=True)

    Eq << apply(GreaterEqual(f(x), y))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

del invert
from . import invert
# created on 2018-02-16
