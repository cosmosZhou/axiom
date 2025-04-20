from util import *


@apply
def apply(given, wrt=None):
    expr, *limits = given.of(Any)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
    else:
        x, S = limit.coerce_setlimit()

    domain = expr.domain_defined(x)
    limit = (x, domain & S)
    limits[i] = limit
    return Any(expr, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    m, n = Symbol(integer=True, positive=True)
    f = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Any[i:Range(m)](f[i] > 0))

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[0], simplify=None)

    Eq << Algebra.Any.given.Any.And.limits.unleash.apply(Eq[1], simplify=None)

    Eq << Eq[-1].this.find(Range).apply(Set.Range.Min.eq.Inter, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Mem_Inter.given.And, simplify=None)

    Eq << Eq[-1].this(i).find(Element[2]).simplify()




if __name__ == '__main__':
    run()
# created on 2022-01-08
