from util import *


@apply
def apply(given):
    p, q = given.of(Equal)
    if not p.is_Bool:
        p, q = q, p

    p = p.of(Bool)
    _p, q = q.of(Mul)
    _p = _p.of(Bool)
    q = q.of(Bool)
    if p != _p:
        S[p], q = q, _p

    return Imply(p, q)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, nonnegative=True)
    f, h, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Equal(Bool(Equal(f[n], g[n])), Bool(Equal(f[n], g[n])) * Bool(Equal(f[n + 1], g[n + 1]))))

    Eq << Eq[0] - Eq[0].rhs

    Eq << Eq[-1].this.lhs.collect(Eq[0].lhs)

    Eq << Algebra.Mul.eq.Zero.to.OrEqS_0.apply(Eq[-1])

    Eq << Eq[-1].this.find(Equal[0]).apply(Algebra.Eq_0.to.Ne, One())

    Eq << Algebra.Or.to.Imply.apply(Eq[-1], pivot=1)

    Eq << Eq[-1].this.lhs.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Bool.eq.Piece)




if __name__ == '__main__':
    run()
# created on 2018-03-21
# updated on 2023-05-14