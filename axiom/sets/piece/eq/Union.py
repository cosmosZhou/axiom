from util import *


@apply
def apply(self):
    (s, et), (universalSet, S[True]) = self.of(Piecewise)
    assert universalSet.is_UniversalSet

    eqs = et.of(And)
    return Equal(self, Union(*(Piecewise((s, eq), (universalSet, True)) for eq in eqs)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    s = Function(etype=dtype.complex[n])
    x, t = Symbol(complex=True, shape=(n,))
    f, g = Function(integer=True, shape=())
    Eq << apply(Piecewise((s(x), (f(x) > 0) & (g(x) > 0)), (x.universalSet, True)))

    Eq.suffice, Eq.necessary = Sets.Eq.of.And.Imply.apply(Eq[0], wrt=t)

    Eq << Eq.suffice.this.find(Element).apply(Algebra.Cond_Piece.to.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.equ.Imply, index=slice(None, 2))

    Eq << Eq[-1].this.rhs.apply(Sets.In_Union.of.Or, simplify=None)

    Eq << Eq[-1].this.rhs.find(Element).apply(Algebra.Cond_Piece.of.Or)

    Eq << Eq[-1].this.rhs.find(Element).apply(Algebra.Cond_Piece.of.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Or.equ.Imply, index=slice(None, 2))

    Eq << Eq.necessary.this.find(Element).apply(Sets.In_Union.to.Or, simplify=None)

    Eq << Eq[-1].this.lhs.find(Element).apply(Algebra.Cond_Piece.to.Or)

    Eq << Eq[-1].this.lhs.find(Element).apply(Algebra.Cond_Piece.to.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.equ.Imply, index=slice(None, 2))

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond_Piece.of.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Or.equ.Imply, index=slice(None, 2))





if __name__ == '__main__':
    run()

# created on 2021-01-24
# updated on 2023-05-20
