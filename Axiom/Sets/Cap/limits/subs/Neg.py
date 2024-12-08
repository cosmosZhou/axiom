from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return Equal(self, limits_subs(Cap, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Sets.Cap.Piece)

    Eq << Eq[-1].this.rhs.apply(Sets.Cap.limits.Neg.oo)

    Eq << Eq[-1].this.rhs.find(Element).apply(Sets.In.Neg)

    Eq << Eq[-1].this.rhs.apply(Sets.Cap.limits.subs.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(Sets.In.Add, c)

    Eq << Eq[-1].this.lhs.apply(Sets.Cap.Piece)


if __name__ == '__main__':
    run()
# created on 2021-01-28
