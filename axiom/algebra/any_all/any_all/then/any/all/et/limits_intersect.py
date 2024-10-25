from util import *


@apply
def apply(any_all_0, any_all_1):
    from axiom.algebra.all.any.then.any.all.et import limits_dependent
    from sympy.concrete.limits import limits_intersect
    (fn0, *limits_f0), *limits_e0 = any_all_0.of(Any[All])
    (fn1, *limits_f1), *limits_e1 = any_all_1.of(Any[All])

    assert not limits_dependent(limits_e0, limits_e1)

    assert len(limits_f0) == len(limits_f1)
    assert all(x == y for (x, *_), (y, *_) in zip(limits_f0, limits_f1))

    limits_f = limits_intersect(limits_f0, limits_f1)
    return Any(All(fn0 & fn1, *limits_f), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    from axiom import algebra

    N, M = Symbol(integer=True)
    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Any[M](All[x:A](f(x) <= M)), Any[N](All[x:B](g(x) <= N)))

    Eq << Eq[-1].this.expr.apply(algebra.all_et.of.et.all)

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(algebra.all.of.all.limits.relax, A)

    Eq << Eq[-1].this.expr.apply(algebra.all.of.all.limits.relax, B)




if __name__ == '__main__':
    run()
# created on 2019-02-24
# updated on 2023-11-12
