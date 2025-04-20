from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    S.of(Cap)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(given.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Element(x, S.expr).simplify()
    return All(contains, *S.limits)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    n = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(Element(x, Cap[k:n](A[k])))

    k = Symbol(domain=Range(n))
    Eq << Eq[0].this.rhs.apply(Set.Cap.eq.Inter.split, {k})

    Eq << Set.Mem.of.Mem_Inter.apply(Eq[-1], index=0)

    Eq << Algebra.All.of.Cond.apply(Eq[-1], k)


if __name__ == '__main__':
    run()

# created on 2021-01-22
