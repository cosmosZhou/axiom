from util import *


@apply
def apply(given, index=0, wrt=None):
    [*eqs], *limits = given.of(All[Or])

    cond = eqs.pop(index)
    if wrt is None:
        wrt = cond.wrt
    else:
        cond._has(wrt)

    cond = cond.invert()

    domain = cond.domain_conditioned(wrt)
    for i, (x, *ab) in enumerate(limits):
        if x == wrt:
            if len(ab) == 2:
                a, b = ab
                assert not b.is_set
                domain = x.range(a, b)
            elif len(ab) == 1:
                domain, = ab
            else:
                continue

            domain &= cond.domain_conditioned(wrt)
            limits[i] = (x, domain)
            return All(Or(*eqs), *limits)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[x:Interval(a, b)]((x <= c) | (f(x) >= 1)), index=0)

    Eq << Algebra.All.of.Or.apply(Eq[1])

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Intersect.of.Or, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.of.Le.real, simplify=None)

    Eq << Algebra.All.to.Or.apply(Eq[0])





if __name__ == '__main__':
    run()

# created on 2019-02-07
# updated on 2024-06-28