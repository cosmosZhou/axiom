from util import *



@apply
def apply(given):
    assert given.is_bool
    return Equal(Bool(given.invert()), 0)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)
    f = Function(shape=(), real=True)

    Eq << apply(GreaterEqual(f(x), y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Bool.eq.Piece)


if __name__ == '__main__':
    run()

# created on 2018-02-17
