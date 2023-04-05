from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    return LessEqual(Abs(self), Expectation(Abs(expr), *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, stats

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << algebra.imply.le.abs.apply(f(x.var))

    Eq << stats.le.imply.le.expect.apply(Eq[-1], (x,), (θ,))

    Eq << algebra.imply.ge.abs.apply(f(x.var))

    Eq << stats.ge.imply.ge.expect.apply(Eq[-1], (x,), (θ,))

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.mul)

    Eq << algebra.le.ge.imply.le.abs.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-04
