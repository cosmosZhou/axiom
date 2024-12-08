from util import *



@apply
def apply(given):
    lhs, S[1] = given.of(Unequal)
    assert lhs.is_Bool
    return Equal(lhs, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Bool(x > y), 1))

    Eq << Eq[0].this.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[1].this.lhs.apply(Algebra.Bool.eq.Piece)


if __name__ == '__main__':
    run()
# created on 2018-01-25
