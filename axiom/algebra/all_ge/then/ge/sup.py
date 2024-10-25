from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    assert Tuple.is_nonemptyset(limits)
    return GreaterEqual(Sup(lhs, *limits).simplify(), Sup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](GreaterEqual(f(i), g(i))))

    Eq << Eq[0].this.expr.reversed

    Eq << -Eq[-1].this.expr

    Eq << algebra.all_ge.then.ge.inf.apply(Eq[-1])

    Eq << -Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-23
