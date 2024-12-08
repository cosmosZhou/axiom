from util import *


@apply
def apply(self):
    A, B = self.of(Intersection)
    function, *limits_a = A.of(Cap)
    S[function], *limits_b = B.of(Cap)
    from Axiom.Sets.Union.eq.Cup.limits.Union import limits_union
    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Cap(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:A](f(k)), Cap[k:B](f(k)), evaluate=False))

    Eq << Eq[0].this.find(Cap).apply(Sets.Cap.Piece)

    Eq << Eq[-1].this.lhs.find(Cap).apply(Sets.Cap.Piece)

    Eq << Eq[-1].this.lhs.find(Cap).apply(Sets.Cap.Piece)

    Eq << Eq[-1].this.lhs.apply(Sets.Intersect.eq.Cap)

    Eq << Eq[-1].this.lhs.expr.apply(Sets.Intersect.eq.Piece)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Piece.unnest)


if __name__ == '__main__':
    run()
# created on 2021-04-28
