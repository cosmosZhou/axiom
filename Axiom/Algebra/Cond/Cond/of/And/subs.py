from util import *

@apply
def apply(given, imply, invert=None, reverse=False):
    if invert:
        old = given.invert()
        new = S.BooleanFalse
    else:
        old = given
        new = S.BooleanTrue

    if reverse:
        old = old.reversed

    _imply = imply._subs(old, new)
    assert _imply != imply
    return given, _imply


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f, g, h = Function(shape=(), integer=True)
    Eq << apply(NotElement(x, S), Equal(Piecewise((f(x), NotElement(x, S)), (g(x), True)), h(x)))

    Eq << Equal(Bool(NotElement(x, S)), 1, plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Equal(Piecewise((f(x), Equal(Bool(NotElement(x, S)), 1)), (g(x), True)), h(x), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap)







if __name__ == '__main__':
    run()

# created on 2018-01-19
# updated on 2023-08-26
