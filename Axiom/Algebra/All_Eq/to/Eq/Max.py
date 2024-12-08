from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Maxima(lhs, *limits).simplify(), Maxima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:Interval(a, b)](Equal(f(x), g(x))))

    x_ = Symbol('x', domain=Interval(a, b))

    Eq << Algebra.All.to.Cond.subs.apply(Eq[0], x, x_)

    Eq << Eq[1].this.lhs.limits_subs(x, x_)

    Eq << Eq[-1].this.rhs.limits_subs(x, x_)

    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()

# created on 2019-01-09
