from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    vars = []
    for x, *ab in self.limits:
        assert not ab
        vars.append((x.var,))
        expr = expr._subs(x, x.var)
    return LessEqual(Inf(expr, *vars), self, evaluate=False)


@prove
def prove(Eq):
    from axiom import stats
    
    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))
    
    Eq << stats.imply.expect_ge.inf.apply(Eq[0].find(Expectation))
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-04-04
