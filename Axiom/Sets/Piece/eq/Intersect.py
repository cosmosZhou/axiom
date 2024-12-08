from util import *


@apply
def apply(self):
    (s, et), (emptySet, S[True]) = self.of(Piecewise)
    assert not emptySet

    eqs = et.of(And)
    return Equal(self, Intersection(*(Piecewise((s, eq), (emptySet, True)) for eq in eqs)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    s = Function(etype=dtype.complex[n])
    x, t = Symbol(complex=True, shape=(n,))
    f, g = Function(integer=True, shape=())
    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.emptySet, True)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0], wrt=t)

    Eq <<= Eq[-2].this.find(Element).apply(Algebra.Cond_Piece.to.Or), \
    Eq[-1].this.find(Element).apply(Sets.In_Intersect.to.And.In)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Intersect.of.And.In, simplify=False), \
    Eq[-1].this.lhs.find(Element).apply(Algebra.Cond_Piece.to.Or)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Algebra.Cond_Piece.of.Or), \
    Eq[-1].this.lhs.find(Element).apply(Algebra.Cond_Piece.to.Or)

    Eq << Eq[-2].this.rhs.apply(Algebra.Cond_Piece.of.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.Or)




if __name__ == '__main__':
    run()

# created on 2018-09-25
# updated on 2023-04-29
