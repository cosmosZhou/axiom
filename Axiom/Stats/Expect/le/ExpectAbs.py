from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    return LessEqual(self, Expectation(Abs(expr), *limits), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Algebra.Le_Abs.apply(f(x.var))

    Eq << Stats.Le.to.Le.Expect.apply(Eq[-1], (x,), (θ,))












if __name__ == '__main__':
    run()
# created on 2023-04-15