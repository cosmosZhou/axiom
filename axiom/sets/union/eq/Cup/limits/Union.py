from util import *


def limits_union(limits, _limits, function=None):
    new_limits = []
    assert len(limits) == len(_limits)

    for limit, _limit in zip(limits, _limits):
        x, domain = limit.coerce_setlimit(function=function)
        S[x], _domain = _limit.coerce_setlimit(function=function)
        new_limits.append((x, domain | _domain))

    return new_limits


@apply
def apply(self):
    A, B = self.of(Union)
    function, *limits_a = A.of(Cup)
    S[function], *limits_b = B.of(Cup)

    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Cup(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(etype=dtype.integer)
    Eq << apply(Union(Cup[k:A](f(k)), Cup[k:B](f(k)), evaluate=False))

#     Eq << Eq[0].this.find(Cup).apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.lhs.find(Cup).apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.lhs.find(Cup).apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.lhs.apply(Sets.Union.eq.Cup)

    Eq << Eq[-1].this.lhs.expr.apply(Sets.Union.eq.Piece, simplify=None)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Piece.unnest)


if __name__ == '__main__':
    run()
# created on 2021-07-13
