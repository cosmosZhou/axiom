from util import *


@apply
def apply(x, y, a, b):
    assert not x.shape and not y.shape
    return LessEqual(abs(x * y - a * b), abs(a) * abs(y - b) + abs(x - a) * abs(y))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x, y, a, b)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.abs)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.abs)

    Eq << Eq[-1].this.rhs.args[0].arg.expand()

    Eq << Eq[-1].this.rhs.args[0].arg.expand()

    Eq << algebra.imply.add_ge.abs.apply(Eq[-1].rhs)

    Eq << Eq[-1].reversed
    


if __name__ == '__main__':
    run()

# created on 2019-10-01
# updated on 2023-06-03
