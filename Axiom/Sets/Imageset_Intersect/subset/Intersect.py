from util import *


@apply
def apply(self):
    expr, (x, ss) = self.of(Cup[FiniteSet, Tuple[Intersection]])
    return Subset(self, Intersection(*(imageset(x, expr, s) for s in ss)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n, m = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=(m,))
    A, B = Symbol(etype=dtype.complex[n])
    Eq << apply(imageset(x, f(x), A & B))

    y = Symbol(complex=True, shape=(m,))
    S = Symbol(Eq[0].lhs)
    S_quote = Symbol("S'", Eq[0].rhs)
    Eq.suffice = Imply(Element(y, S), Element(y, S_quote), plausible=True)

    Eq << Eq.suffice.this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Sets.In_Intersect.of.And, simplify=False)

    Eq << Eq[-1].apply(Algebra.Imply.of.And.Imply)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.rhs.apply(Sets.Cup.eq.Union.split, cond=B), Eq[-1].this.rhs.rhs.apply(Sets.Cup.eq.Union.split, cond=A)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Union.of.Or, simplify=False), Eq[-1].this.rhs.apply(Sets.In_Union.of.Or, simplify=False)

    Eq << Sets.Imply.to.Subset.apply(Eq.suffice)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()

# created on 2021-04-26
