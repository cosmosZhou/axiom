from util import *



@apply
def apply(given):
    p, q = given.of(Imply)

    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Imply(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Imply(Equal(Bool(Eq[0].lhs), 1), Equal(Bool(Eq[0].rhs), 1), plausible=True)

    Eq << Eq[-1].this.lhs.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-2].apply(Algebra.Imply.to.Or)

    Eq << Eq[-1].this.args[1].apply(Algebra.Ne.to.Eq_0.Bool)

    Eq << Algebra.Or.to.Eq_0.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2018-01-27
