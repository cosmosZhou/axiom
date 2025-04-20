from util import *


@apply
def apply(Any_All_0, Any_All_1):
    from Axiom.Algebra.Any.All.And.of.All.Any import limits_dependent
    (fn0, *limits_f0), *limits_e0 = Any_All_0.of(Any[All])
    (fn1, *limits_f1), *limits_e1 = Any_All_1.of(Any[All])

    assert not limits_dependent(limits_e0, limits_e1)
    assert not limits_dependent(limits_f0, limits_f1)

    return Any(All(fn0 & fn1, *limits_f0, *limits_f1), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    N, M = Symbol(integer=True)
    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(Any[M](All[x:A](f(x) <= M)), Any[N](All[y:B](g(y) <= N)))

    Eq << Eq[-1].this.expr.apply(Algebra.All_And.given.And.All)

    Eq << Algebra.And.given.And.apply(Eq[-1])

    Eq << Logic.Or.given.Cond.apply(Eq[-2], 1)

    Eq << Logic.Or.given.Cond.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()

# created on 2019-02-24
from . import limits_Inter
