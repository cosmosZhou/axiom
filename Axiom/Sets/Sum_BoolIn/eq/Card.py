from util import *


@apply
def apply(s, wrt=None):
    assert s.is_set
    if wrt is None:
        wrt = s.generate_var(**s.etype.dict)
    return Equal(Sum[wrt:s](Bool(Element(wrt, s))), Card(s))


@prove
def prove(Eq):
    from Axiom import Algebra
    S = Symbol(etype=dtype.integer)

    Eq << apply(S)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.lhs().expr.simplify()


if __name__ == '__main__':
    run()

# created on 2020-07-03
