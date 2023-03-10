from util import *


@apply
def apply(any_all, all):
    from sympy.concrete.limits import limits_union
    forall0, *limits_e = any_all.of(Any)

    cond, *limits_f0 = forall0.of(All)
    _cond, *limits_f1 = all.of(All)
    assert forall0.variables == all.variables
    assert _cond == _cond

    limits_f = limits_union(limits_f0, limits_f1)
    return Any(All(cond, *limits_f), *limits_e)


@prove
def prove(Eq):
    from axiom import algebra

    N, n = Symbol(integer=True)
    g, f = Function(shape=(), integer=True)
    M = Symbol(g(N))
    Eq << apply(Any[N](All[n:N:oo](f(n) <= M)), All[n:N](f(n) <= M))

    Eq << Eq[0].this.expr.apply(algebra.all.all.imply.all.limits_union, Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-02-23
