from util import *


@apply
def apply(self):
    d, S[d] = self.of(Ceiling[Sign / Expr])
    assert d.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    d = Symbol(integer=True, zero=False, given=True)
    Eq << apply(Ceiling(sign(d) / d))

    Eq << Sets.Eq_Ceiling.of.In.Interval.apply(Eq[0])

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.find(Sign).apply(Algebra.Sign.eq.Piece.Abs)

    Eq << Eq[-1].this.find(Sign).apply(Algebra.Sign.eq.Piece.Abs)

    Eq << Eq[-1] * abs(d)

    Eq << ~Eq[-1].reversed

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-29
