from util import *


@apply
def apply(given, old, new):
    cond, *limits = given.of(All)
    for i, (x, *args) in enumerate(limits):
        if x == old:
            break
    else:
        return
    limits_prior = limits[:i]
    limit = limits[i]
    limits_post = limits[i + 1:]
    from Axiom.Algebra.All.to.Cond.subs import extract
    S[old], domain = extract(*limit)
    if domain.is_set:
        assert domain.conditionally_contains(new)
    elif domain.is_bool:
        assert domain._subs(old, new)
    else:
        return

    if limits_prior:
        cond = All(cond, *limits_prior)

    cond = cond._subs(old, new)
    assert limits_post
    return All(cond, *limits_post)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, i, m = Symbol(integer=True)
    n = Function(integer=True, nonnegative=True)
    f = Function(shape=(), integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(All[x:n(i) + 1, i:m](Element(f(x), s)), x, n(i))

    Eq << Algebra.All.to.Or.limits_delete.apply(Eq[0], 1)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.to.Cond.subs, x, n(i))

    Eq << Algebra.Or.to.All.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()
# created on 2024-06-25