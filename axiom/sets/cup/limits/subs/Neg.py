from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return Equal(self, limits_subs(Cup, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.limits.Neg.oo)

    Eq << Eq[-1].this.rhs.find(Element).apply(Sets.In.Neg)

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.limits.subs.offset, -c)


if __name__ == '__main__':
    run()
# created on 2018-10-07
