from util import *


@apply
def apply(subset, exist):
    expr, *limits = exist.of(Any)

    B, A = subset.of(Subset)

    for index, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == B:
                break
        elif len(domain) == 2:
            if x.range(*domain) == B:
                break
    else:
        return

    limits[index] = (x, A)
    return Any(expr, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n])
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=())
    Eq << apply(Subset(B, A), Any[x:B](f(x) > 1))

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[1], simplify=None)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Set.Mem.of.Mem.Subset)




if __name__ == '__main__':
    run()
# created on 2019-07-10
# updated on 2023-05-18
