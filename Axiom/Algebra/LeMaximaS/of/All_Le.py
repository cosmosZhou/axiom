from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[LessEqual])
    assert Tuple.is_nonemptyset(limits)
    return LessEqual(Maxima(lhs, *limits).simplify(), Maxima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](LessEqual(f(i), g(i))))

    Eq << Eq[0].this.expr.reversed

    Eq << Algebra.GeMaximaS.of.All_Ge.apply(Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-23
