from util import *


@apply
def apply(any_eq, forall, reverse=False):
    (x, y), *limits = any_eq.of(Any[Equal])
    cond, *S[limits] = forall.of(All)

    if reverse:
        x, y = y, x
    return Any(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    S = Symbol(etype=dtype.integer)

    Eq << apply(Any[x:S](Equal(g(x), f(x))), All[x:S](g(x) > y))

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)


if __name__ == '__main__':
    run()

# created on 2019-02-25
